{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, TupleSections #-}
{-# LANGUAGE LambdaCase #-}

module Simplify.ConcreteToAbstract 
  (cs2as) where

import Types.ConcreteSyntax
import qualified Types.SourceAbstractSyntax as S

import CCO.Component
import CCO.Feedback
import CCO.Printing

import Control.Applicative
import Control.Monad.Except

import Data.Either (rights)
import Data.Foldable (foldrM)
import qualified Data.Map as M

instance MonadError String Feedback where
    throwError = errorMessage . wrapped

cs2as :: Bool -> Component CBSFile S.CBSFile 
cs2as gen_ph = component (sFile gen_ph)

sFile :: MonadError String m => Bool -> CBSFile -> m S.CBSFile
sFile gen_ph file = toFile =<< sFilterSpecs gen_ph Nothing file
  where toFile (als, vardecls, specs) = do
          vts <- forM vardecls $ \decl -> case decl of 
              VarDeclSubType x t  -> (:[]) . (x,) . S.SubTyOf <$> sSort t
              VarDeclType x t     -> (:[]) . (x,) . S.ElemOf <$> sSort t
          return (S.CBSFile specs (M.fromList (concat vts)) (M.fromListWith (++) als))

sFilterSpecs :: MonadError String m => 
  Bool -> (Maybe [CommentPart]) -> [CBSSpec] 
       -> m ([(Name, [Name])], [VarDecl], [S.CBSSpec])
sFilterSpecs _ _ [] = return ([], [], [])
sFilterSpecs gen_ph mdoc (f@(FunconSpec _ _ _ _):c@(CommentSpec _):r@(RuleSpec _):rest)
  = sFilterSpecs gen_ph mdoc (c:f:r:rest)
sFilterSpecs gen_ph mdoc (spec:specs) = case spec of 
 -- completely ignore entity declarations (CBS-beta)
  EntitySpec _ -> sFilterSpecs gen_ph Nothing specs
  FunconSpec _ _ _ (Just (DefRewrite TermDots)) | not gen_ph -> 
    sFilterSpecs gen_ph Nothing specs 
  FunconSpec nm _ _ _ -> 
    let (relatedspecs, otherspecs') = span isRelated specs
        otherspecs   = aliases ++ otherspecs'
        (aliases, rulespecs) = foldr op ([], []) relatedspecs
          where op a@(AliasSpec _ _) (as,rs)   = (a:as,rs)
                op r@(RuleSpec _)    (as,rs)   = (as,r:rs)
                op _                 acc       = acc
        isRelated (AliasSpec _ _) = True
        isRelated (CommentSpec _) = True
        isRelated spec = isFunconRuleSpec spec 
        isFunconRuleSpec (RuleSpec r) = case r of 
          Inference _ conc  -> nm == termName (concSource conc)
          _                 -> False
        isFunconRuleSpec _            = False
    in do spec <- sSpec spec mdoc (map (\(RuleSpec r) -> r) rulespecs)
          (als,decls,specs) <- sFilterSpecs gen_ph Nothing otherspecs
          return (als, decls, spec:specs)
  CommentSpec parts -> case specs of
    ((FunconSpec _ _ _ _):otherspecs) -> sFilterSpecs gen_ph Nothing specs
    otherspecs -> sFilterSpecs gen_ph Nothing specs
  TypeSpec _ _ _ (Just (DefRewrite TermDots)) 
    | not gen_ph -> sFilterSpecs gen_ph Nothing specs
  LexisSpec _ -> sFilterSpecs gen_ph Nothing specs
  SyntaxSpec _ -> sFilterSpecs gen_ph Nothing specs
  SemanticsSpec _ _ _ _ _ _ -> sFilterSpecs gen_ph Nothing specs
  RuleSpec _ -> sFilterSpecs gen_ph Nothing specs
  OtherwiseSpec _ -> sFilterSpecs gen_ph Nothing specs
  AliasSpec t f -> do (als, decls, specs) <- sFilterSpecs gen_ph Nothing specs  
                      return ((f,[t]):als,decls,specs)
  MetaVariablesSpec ds -> do  (als, decls, specs) <- sFilterSpecs gen_ph Nothing specs 
                              return (als, ds++decls,specs) 
  _ -> do spec <- sSpec spec mdoc []
          (als, decls, specs) <- sFilterSpecs gen_ph Nothing specs
          return (als, decls, (spec:specs))

sSpec :: MonadError String m => CBSSpec -> (Maybe [CommentPart]) -> [Rule] -> m S.CBSSpec
sSpec spec mdoc rules = case spec of
  MetaSpec s -> return (S.MetaSpec s)
  Auxiliary s -> sSpec s mdoc rules
  FunconSpec nm mparams ty mcs -> do
    sig <- buildFSig nm mparams ty mdoc
    case mcs of
      Just (DefRewrite term) -> S.FunconSpec . S.FAbbrv sig <$> sMaybeTerm term
      _                      -> S.FunconSpec . S.FRules sig <$> sRules rules
  TypeSpec nm mparams _ Nothing -> S.TypeSpec <$> decl
    where decl = S.DataTypeDecl nm <$> params <*> return []
          params = maybe (return []) (mapM sValParam) mparams
  TypeSpec nm mparams _ tcs -> (S.TypeSynonymSpec <$>) $ case tcs of
    Just (DefRewrite ty) -> S.TypeSynonymDecl nm <$> params <*> sSort ty
      where params = maybe (return []) (mapM sValParam) mparams
    _ -> throwError ("unexpected type synonym: " ++ nm)
  DatatypeSpec nm mparams mbound alts -> S.DataTypeSpec <$> decl
    where decl = S.DataTypeDecl nm <$> params <*> sAlts alts 
          params = maybe (return []) (mapM sValParam) mparams
          sAlts = mapM sAlt
          sAlt alt = case alt of 
            Inj _ ty -> S.DataTypeInclusion <$> sSort ty
            Cons nm mparams -> S.DataTypeConstructor nm <$> mapM sSortOfParam params
              where params = maybe [] id mparams
            AltDots -> throwError "undefined datatype alternative"
  _ -> throwError "unexpected lexis/syntax/semantics specification"

sSortOfParam :: MonadError String m => Param -> m S.FSort 
sSortOfParam p = case p of
  Param _ (Just (InType ty)) -> sSort ty
  Param _ (Just (Sup ty))    -> sSort ty
  _ -> throwError ("unexpected type parameter: "  ++ show p)

sValParam :: MonadError String m => Param -> m S.FParam
sValParam (Param var mbound) = case mbound of
  Nothing     -> return (mkVar var, Nothing)
  Just bound  -> case bound of
    Sub ty      -> (mkVar var,) . Just <$> bValSort ty
    Sup ty      -> (mkVar var,) . Just <$> bValSort (TermName "values")
    InType ty   -> (mkVar var,) . Just <$> bValSort ty
  where mkVar var = case var of 
          Nothing -> S.PPAny
          Just str -> case last str of
                          '*' -> S.PPSeqMetaVar str S.StarOp
                          '?' -> S.PPSeqMetaVar str S.QuestionMarkOp
                          '+' -> S.PPSeqMetaVar str S.PlusOp
                          _   -> S.PPMetaVar str

buildFSig :: MonadError String m => 
  Name -> Maybe Params -> Term -> Maybe [CommentPart] -> m S.FSig
buildFSig nm mparams ty mdoc = do
  params <- maybe (return []) (mapM sValParam) mparams
  S.FSig nm params <$> bValSort ty <*> sMDoc mdoc

sMDoc :: MonadError String m => Maybe [CommentPart] -> m (Maybe [S.CommentPart])
sMDoc Nothing = return Nothing
sMDoc (Just cs) = Just <$> mapM sCommentPart cs

sCommentPart :: MonadError String m => CommentPart -> m S.CommentPart
sCommentPart (Ordinary o)         = return $ S.Ordinary o
sCommentPart (Asterisk)           = return $ S.Asterisk
sCommentPart (At s)               = return $ S.At s
sCommentPart (CommentTerm t)      = return $ S.CommentTerm t
sCommentPart (CommentPremise f)   = return $ S.CommentPremise f
sCommentPart (SpecInComment spec) = S.SpecInComment <$> sSpec spec Nothing []

bValSort :: MonadError String m => Type -> m S.FSort
bValSort ty = case ty of 
                TermTuple    [t2] -> bValSort t2
                _                 -> sTerm ty

sMaybeTerm :: MonadError String m => Term -> m (Maybe S.FTerm)
sMaybeTerm TermDots = return Nothing
sMaybeTerm t = Just <$> sTerm t

sTerm :: MonadError String m => Term -> m S.FTerm
sTerm t = case t of
  TermDots -> return (S.TTuple [])
  TermVar Nothing     -> return $ S.TAny
  TermVar (Just var)  -> return $ S.TMetaVar var
  TermConst cnst      -> case cnst of
    ConstAtom a         -> return $ S.TLiteral (S.FLiteralString a)
    ConstString str     -> return $ S.TLiteral (S.FLiteralString str)
    ConstNat n          -> return $ S.TLiteral (S.FLiteralNat n)
    ConstFloat f        -> throwError "CBS compiler does not support float constants"
  TermName nm         -> return $ S.TName nm
  VarApp var term     -> throwError ("CBS compiler does not support variable application: " ++ show var)
  NameApp nm (TermTuple terms)     
                      -> S.TApp nm <$> mapM sTerm terms
  NameApp nm term     -> S.TApp nm . (:[]) <$> sTerm term
  Typed term ty       -> sTerm term --throwError ("unexpected typed term: " ++ show (term,ty))
  Computes ty         -> S.TSortComputes <$> sTerm ty
  ComputesFrom f t    -> S.TSortComputesFrom <$> sTerm f <*> sTerm t
  TermPostfix t op    -> flip S.TSortSeq op <$> sTerm t 
  TermSequence ts     -> throwError "top-level term-sequence" 
  TermTuple ts        -> S.TTuple <$> mapM sTerm ts
  TermList  ts        -> S.TList <$> mapM sTerm ts
  TermSet ts          -> S.TSet <$> mapM sTerm ts
  TermMap ps          -> S.TMap . concat <$> mapM sPoint ps
    where sPoint Nothing      = throwError "... in map literal"
          sPoint (Just (f,t)) = (\a b -> [a,b]) <$> sTerm f <*> sTerm t
  TermUnion t1 t2     -> S.TSortUnion <$> sTerm t1 <*> sTerm t2
  TermInter t1 t2     -> S.TSortInter <$> sTerm t1 <*> sTerm t2
  TermPower t1 t2     -> S.TSortPower <$> sTerm t1 <*> sTerm t2
  TermComplement ty   -> S.TSortComplement <$> sTerm ty
 
  SemanticsApp _ _ _  -> throwError "unexpected semantic application in term"
 
sRules :: MonadError String m => [Rule] -> m [S.FRule]
sRules = mapM sRule

sRule :: MonadError String m => Rule -> m S.FRule
sRule r = case r of
  Inference _ (ConcStatic _ _ _ _ _) -> throwError "missing translation for static rules"
  Inference _ (ConcTyping _ _ _) -> throwError "missing translation for typing rules"
  Desugar _ _ _ -> error "translating desugar rule"
  Semantics _ _ _ _ -> error "translation semantics rule"
  Inference scs (ConcRewrite t1 t2) -> rewriteRule t1 t2 scs
  Inference scs (ConcDynamic mc st1 arr st2) -> stepRule mc st1 st2 arr scs 
 where  nmOfTerm t = case t of
          TermName nm   -> return nm
          NameApp nm _  -> return nm
          _             -> throwError ("invalid rule pattern: " ++ show t)
        patsOf t = case t of
          TermName nm     -> return Nothing
          NameApp _ (TermTuple []) -> return Nothing
          NameApp _ term  -> Just <$> term2pats term
          _               -> throwError ("invalid rule pattern: " ++ show t)

        rewriteRule :: MonadError String m => 
          Term -> Term -> [Premise] -> m S.FRule
        rewriteRule t1 t2 scs = do
          S.FRuleRewrite (termName t1) 
            <$> case termArgs t1 of 
                  Nothing   -> return Nothing
                  Just args -> Just <$> mapM term2pat args
            <*> fmap Just (sTerm t2)
            <*> prem2sideconds scs

        stepRule :: MonadError String m => 
          (Maybe Context) -> State -> State -> Dynamic -> [Premise] -> m S.FRule
        stepRule mc s1 s2 arr prs = do
          source <- case termArgs (stateTerm s1) of
                      Nothing   -> return Nothing
                      Just args -> Just <$> mapM term2pat args
          target <- sTerm (stateTerm s2)
          inhs <- sEntities term2pat (contextEnts mc)
          muts_in <- sEntities term2pat (stateEnts s1)
          muts_out <- sEntities sTerm (stateEnts s2)
          (inps, outs, ctrs) <- foldrM arrowEnts ([], [], []) (dynamicEnts arr)
          let fstep = S.FStep source target inhs (muts_in, muts_out) inps outs ctrs
          S.FRuleStep (termName t1) fstep <$> prem2conds prs
          where t1 = stateTerm s1
                muts_in = stateEnts s1
                t2 = stateTerm s2
                muts_out = stateEnts s2
                arrowEnts (n,t,pol) (is, os, cs) = case pol of
                  Nothing   -> (\t' -> (is,os,(n,t'):cs)) <$> term2pat t
                  Just In   -> (\t' -> ((n,t'):is,os,cs)) <$> term2pat t
                  Just Out  -> (\t' -> (is,(n,t'):os,cs)) <$> sTerm t
{-
          mpats <- patsOf t1
          target <- sTerm t2
          context <- sMaybeContext term2pat mc
          muts_pat <- sMutEntities term2pat muts_in
          muts_term <- sMutEntities sTerm muts_out
          (ins, outs, sigs) <- sArrow term2pat sTerm term2pat arr
          let step = S.FStep mpats target context (muts_pat, muts_term) ins outs sigs 
          nm <- nmOfTerm t1
          antecedents <- forms2prems scs
          return (S.FRuleStep nm step antecedents)
-}

term2pats :: MonadError String m => Term -> m [S.FPattern]
term2pats term = case term of
    TermSequence ts -> terms2pats ts
    TermTuple ts -> terms2pats ts 
    _            -> (:[]) <$> term2pat term 

terms2pats :: MonadError String m => [Term] -> m [S.FPattern]
terms2pats = mapM term2pat

term2pat :: MonadError String m => Term -> m S.FPattern
term2pat t = case t of
  TermConst cnst    -> case cnst of
    ConstAtom str     -> return $ S.PLit (S.FLiteralAtom str)
    ConstString str   -> return $ S.PLit (S.FLiteralString str)
    ConstNat n        -> return $ S.PLit (S.FLiteralNat n)
    ConstFloat f      -> return $ S.PLit (S.FLiteralFloat f)
  TermVar (Just var)    
    | last var == '*' -> return $ S.PSeqMetaVar var S.StarOp
    | last var == '+' -> return $ S.PSeqMetaVar var S.PlusOp
    | last var == '?' -> return $ S.PSeqMetaVar var S.QuestionMarkOp
    | otherwise       -> return $ S.PMetaVar var
  TermVar Nothing   -> return $ S.PAny
  TermDots          -> return $ S.PAny
  TermName nm       -> return $ S.PADT nm []
  NameApp nm term   -> S.PADT nm <$> term2pats term
  VarApp var term   -> throwError "variable application not allowed in a pattern"
  Typed term ty     -> S.PAnnotated <$> term2pat term <*> sSort ty
  Computes _        -> throwError " =>_ appearing in pattern"
  ComputesFrom _ _  -> throwError " _=>_ appearing in pattern"
  TermPostfix (TermVar Nothing) op  -> return $ S.PSeqMetaVar "___" op 
  TermPostfix TermDots op           -> return $ S.PSeqMetaVar "___" op
  TermPostfix _ _   -> throwError "postfix in pattern"
  TermSequence ts   -> throwError "top-level term-sequence in pattern" 
  TermUnion _ _     -> throwError "sort-union in pattern"
  TermInter _ _     -> throwError "sort-intersect in pattern"
  TermComplement _  -> throwError "sort-complement in pattern"
  TermTuple ts      -> S.PTuple <$> terms2pats ts
  TermList ts       -> S.PList <$> terms2pats ts
  TermSet ts        -> throwError "set notation in pattern" 
  TermMap ts        -> throwError "map notation in pattern"
  TermPower t1 t2   -> throwError "term power in pattern"
  SemanticsApp _ _ _-> throwError "unexpected semantic application in pattern"

prem2sideconds :: MonadError String m => [Premise] -> m [S.FSideCondition]
prem2sideconds prems = concat <$> mapM filterOp prems
  where filterOp prem = rights <$> prem2cond prem

prem2conds :: MonadError String m => [Premise] -> m [Either S.FPremiseStep S.FSideCondition]
prem2conds prems = concat <$> mapM prem2cond prems

prem2cond :: MonadError String m => Premise -> m [Either S.FPremiseStep S.FSideCondition]
prem2cond prem = case prem of 
  PremStatic _ _ _ _ _ -> 
    throwError "missing translation for static premises"
  PremTyping (Just _) _ _ -> 
    throwError "missing translation for typing premises"
  PremTyping _ (StateExplicit _ _) _ -> 
    throwError "missing translation for typing premises"
  PremDynamic mc st1 arr st2 -> 
    (:[]) . Left <$> bPremiseStep mc st1 arr st2 
  PremRewrite t1 t2 -> 
    (((:[]) . Right) .) . S.SCPatternMatch <$> sTerm t1 <*> term2pat t2
  PremEquality t1 t2 -> 
    (((:[]) . Right) .) . S.SCEquality <$> sTerm t1 <*> sTerm t2
  PremInequality t1 t2 -> 
    (((:[]) . Right) .) . S.SCInequality <$> sTerm t1 <*> sTerm t2
  PremTyping Nothing (StateImplicit t1) t2 -> 
    (((:[]) . Right) .) . S.SCIsInSort <$> sTerm t1 <*> sSort t2
  PremSubtype t1 t2 -> 
    return []

bPremiseStep :: MonadError String m => 
  Maybe Context -> State -> Dynamic -> State -> m S.FPremiseStep
bPremiseStep mc lhs arr rhs = do 
  source <- sTerm (stateTerm lhs)
  target <- term2pat (stateTerm rhs)
  inhs <- sEntities sTerm (contextEnts mc)
  muts_in <- sEntities sTerm (stateEnts lhs)
  muts_out <- sEntities term2pat (stateEnts rhs)
  (inps,outs,ctrs) <- foldrM op ([],[],[]) (dynamicEnts arr)
  return (S.FPremiseStep source target inhs (muts_in,muts_out) inps outs ctrs)
  where op (n,t,pol) (is, os, cs) = case pol of
          Nothing   -> (\t' -> (is,os,(n,t'):cs)) <$> term2pat t
          Just In   -> (\t' -> ((n,t'):is,os,cs)) <$> sTerm t
          Just Out  -> (\t' -> (is,(n,t'):os,cs)) <$> term2pat t

sEntities :: MonadError String m => (Term -> m a) -> [EntTerm] -> m [(Name, a)]
sEntities simplifier = mapM op
 where op (nm, t) = (nm,) <$> simplifier t
{-
sArrow :: MonadError String m => 
          (Term -> m ins) -> (Term -> m outs) -> (Term -> m sigs) -> 
            Arrow -> m ([(Name, ins)],[(Name, outs)],[(Name, sigs)])
sArrow sIns sOuts sSigs arr = case arr of
  Normal es -> mkEntities es
  Static es -> mkEntities es
  Rewrite   -> mkEntities []
  where mkEntities = foldM op ([],[],[]) 
          where op (ins,outs,sigs) (EmitIn nm term) = do
                  s <- sIns term
                  return ((nm,s):ins,outs,sigs)
                op (ins,outs,sigs) (EmitOut nm term) = do
                  s <- sOuts term
                  return (ins,(nm,s):outs,sigs)
                op (ins,outs,sigs) (EmitSig nm term) = do
                  s <- sSigs term
                  return (ins,outs,(nm,s):sigs)
-}
sSort :: MonadError String m => Term -> m S.FSort
sSort = sTerm

