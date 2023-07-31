{-# Language FlexibleContexts, LambdaCase, MultiParamTypeClasses, TupleSections, FlexibleInstances, OverloadedStrings #-}

module Simplify.Simplifier where

import Funcons.EDSL (Values(..), Funcons(..), string__)
import qualified Funcons.EDSL as EDSL

import CCO.Component (Component, component)
import CCO.Feedback (Feedback, errorMessage)
import CCO.Printing (wrapped)

import Control.Applicative
import Control.Monad.Except

import Data.Either
import Data.Monoid
import Data.Text (pack)
import qualified Data.Map as M
import qualified Data.Set as S 

import Simplify.Utils

--------------------------------------------------------------------

import Types.Bindings
import Types.SourceAbstractSyntax
import qualified Types.CoreAbstractSyntax as C

--------------------------------------------------------------------

-- require for forming a pipeline with uu-cco library
simplifier :: Component CBSFile C.CBSFile
simplifier = component simplifyCBSFile

instance MonadError String Feedback where
    throwError = errorMessage . wrapped

--------------------------------------------------------------------

simplifyCBSFile :: MonadError String m => CBSFile -> m C.CBSFile
simplifyCBSFile (CBSFile file env als) = do
  env' <- simplifyTypeEnv env 
  let kindMap = foldr bindTypeDecl M.empty file
  specss <- mapM (simplifyCBSSpec kindMap env') file 
  let specs = map (mvarConditions env') (concat specss)
  return $ C.CBSFile specs env' als

bindTypeDecl :: CBSSpec -> KindMap -> KindMap
bindTypeDecl (TypeSpec (DataTypeDecl nm _ _)) = M.insert nm Type
bindTypeDecl (DataTypeSpec (DataTypeDecl nm _ _)) = M.insert nm DataType 
bindTypeDecl _ = id

mvarConditions :: C.TypeEnv -> C.CBSSpec -> C.CBSSpec
mvarConditions env s = case s of 
  C.FunconSpec (C.FRules nm sig mcs rs ss)  
    -> C.FunconSpec (C.FRules nm sig mcs rs' ss')
    where rs' = map mvarRs rs
          ss' = map mvarSs ss
  _ -> s
  where mvarRs r@(C.FRewriteRule p f ss) = 
            -- added last to ensure bindings
          C.FRewriteRule p f (ss ++ M.foldrWithKey op [] env)
          where op x (C.ElemOf ty) acc = case x `S.member` patvars of
                                True  -> C.SCIsInSort (C.TVar x) ty : acc
                                False -> acc
                op x (C.SubTyOf _) acc = acc
                patvars = pvars r
        mvarSs r@(C.FStepRule f scs) = C.FStepRule f (scs ++ M.foldrWithKey op [] env)
          where patvars = pvars r
                op x (C.ElemOf ty) acc = case x `S.member` patvars of
                                True  -> Right (C.SCIsInSort (C.TVar x) ty) : acc
                                False -> acc
                op x (C.SubTyOf _) acc = acc

-- add side-conditions to rules based on the declarations of meta-variables

simplifyTypeEnv :: MonadError String m => TypeEnv -> m C.TypeEnv
simplifyTypeEnv = mapM simplifyTyAssoc

simplifyTyAssoc :: MonadError String m => TyAssoc -> m C.TyAssoc
simplifyTyAssoc (ElemOf t) = C.ElemOf <$> simplifyFTerm t
simplifyTyAssoc (SubTyOf t) = C.SubTyOf <$> simplifyFTerm t

type KindMap = M.Map Name {- type name -} Kind
data Kind = DataType | Type deriving (Show, Enum)

simplifyCBSSpec :: MonadError String m => KindMap -> C.TypeEnv -> CBSSpec -> m [C.CBSSpec]
simplifyCBSSpec _ _ (TypeSynonymSpec spec) = return . C.FunconSpec   <$> simplifyTypeSynonymSpec spec
simplifyCBSSpec km tyenv (TypeSpec spec) = simplifyCBSSpec km tyenv (DataTypeSpec spec)
simplifyCBSSpec _ tyenv (DataTypeSpec spec@(DataTypeDecl tynm typarams alts)) = do 
  conss <- forM alts $ \alt -> case alt of 
    DataTypeInclusion _ -> return mzero
    DataTypeConstructor nm sorts -> do 
      sorts' <- mapM simplifyFTerm sorts
      typarams' <- mapM (simplifyParamPattern tyenv) typarams
      return [genDataValCons tynm typarams' nm sorts']
  dspec <- simplifyDataTypeSpec tyenv spec
  return (C.DataTypeSpec dspec : msum conss)
simplifyCBSSpec km _ (FunconSpec spec@(FRules sig rules))
  | Just (tyname, kind) <- mNameKind -- recognised as a value-constructor
  , null rules                       -- and definition is missing
    = do  args <- mapM sortInPattern (sigParams sig)
          typarams <- maybe (return []) (mapM toTypeParam) $ termArgs (sigSort sig)
          sig' <- mkCSig kind
          return [C.ConsSpec (C.ValCons (sigName sig) sig'
                  args tyname typarams)]
      where toTypeParam t = term2tpat <$> simplifyFTerm t
            mNameKind = case sigSort sig of
                TName tnm   -> fmap (tnm,) (M.lookup tnm km)
                TApp tnm _  -> fmap (tnm,) (M.lookup tnm km)
                _           -> Nothing
              where nameOf (TName nm)   = nm
                    nameOf (TApp nm _)  = nm
                    nameOf t            = error ("nameOf assert1: " ++ show t)
            mkCSig kind = case kind of 
              DataType -> return C.DataTypeCons
              Type     -> C.TypeCons <$> simplifyFSig sig
            sortInPattern (_, Nothing) = throwError ("constructor " ++ (sigName sig) ++ " without typed arguments")
            sortInPattern (_, Just sort) = simplifyFTerm sort
 
simplifyCBSSpec _ _ (FunconSpec spec) = return . C.FunconSpec   <$> simplifyFunconSpec spec
simplifyCBSSpec _ _ (EntitySpec spec)      = return . C.EntitySpec   <$> simplifyEntitySpec spec
simplifyCBSSpec _ _ (MetaSpec spec)        = return . return $ C.MetaSpec spec 

simplifyTypeSynonymSpec :: MonadError String m => TypeSynonymSpec -> m C.FunconSpec
simplifyTypeSynonymSpec (TypeSynonymDecl n ps ty) =
    simplifyFunconSpec $ 
      FAbbrv (FSig n ps (TName "types") Nothing) (Just ty)

genDataValCons :: Name -> [C.TPattern] -> Name -> [C.FSort] -> C.CBSSpec
genDataValCons tynm typarams nm ptypes = 
  C.ConsSpec (C.ValCons nm C.DataTypeCons ptypes tynm typarams)

simplifyDataTypeSpec :: MonadError String m => C.TypeEnv -> DataTypeSpec -> m C.DataTypeSpec
simplifyDataTypeSpec tyenv (DataTypeDecl nm ps alts) =
        C.DataTypeDecl nm <$> mapM (simplifyParamPattern tyenv) ps <*> simplifyDataTypeAlts alts

simplifyParamPattern :: MonadError String m => 
  C.TypeEnv -> FParam -> m (C.TPattern)
simplifyParamPattern tyenv (pat,_) = simplifyPat pat 
  where  simplifyPat (PPMetaVar var) = return $ C.TPVar var 
         simplifyPat PPAny = return $ C.TPWildCard
         simplifyPat (PPSeqMetaVar var op) = return $ C.TPSeqVar var op

simplifyDataTypeAlts :: MonadError String m => [DataTypeAlt] -> m [C.DataTypeAlt]
simplifyDataTypeAlts alts = concat <$> mapM simplifyDataTypeAlt alts
simplifyDataTypeAlt :: MonadError String m => DataTypeAlt -> m [C.DataTypeAlt]
simplifyDataTypeAlt (DataTypeInclusion term) = 
  return . C.DataTypeInclusion <$> simplifyFTerm term
simplifyDataTypeAlt (DataTypeConstructor nm terms) = return []

simplifyEntitySpec :: MonadError String m => EntitySpec -> m C.EntitySpec
simplifyEntitySpec (InheritedSpec (name,term,_))
  = C.InheritedSpec name <$> simplifyFTerm term
simplifyEntitySpec (MutableSpec (name1,term,ty1) (name2,_,ty2))
  = do guardM (name1 == name2) "mutable entity name mismatch"
       guardM (ty1 == ty2) "mutable entity type mismatch"
       C.MutableSpec name1 <$> simplifyFTerm term

simplifyEntitySpec (InputSpec (name,_,ty)) =
     return (C.InputSpec name)

simplifyEntitySpec (OutputSpec (name,_,ty)) =
  do guardM (isAppOf "lists" ty) "output entities must be declared to contain lists"
     return (C.OutputSpec name)

simplifyEntitySpec (ControlSpec (name,ty)) =
  do guardM (isSortSeq QuestionMarkOp ty) "control entities must be declared to contain option types `(T)?`"
     return (C.ControlSpec name)


simplifyFunconSpec :: MonadError String m => FunconSpec -> m C.FunconSpec

simplifyFunconSpec (FAbbrv sig mterm)
  = do term' <- maybe (return Nothing) ((Just <$>) . simplifyFTerm) mterm
       mdoc  <- sMDoc (sigDoc sig)
       params <- mapM abbrvParamPatt (sigParams sig)
       sig' <- simplifyFSig sig
       return $ C.FRules (sigName sig) sig' mdoc 
                    [ C.FRewriteRule params term' [] ] []
simplifyFunconSpec (FRules sig rules) = do
  mdoc <- sMDoc (sigDoc sig)
  sig' <- simplifyFSig sig
  uncurry (C.FRules n sig'  mdoc) <$> simplifyFRules n rules
  where
    n = sigName sig


sMDoc :: MonadError String m => Maybe [CommentPart] -> m (Maybe [C.CommentPart])
sMDoc Nothing = return Nothing
sMDoc (Just cs) = Just <$> mapM sCommentPart cs

sCommentPart :: MonadError String m => CommentPart -> m C.CommentPart
sCommentPart (Ordinary o)         = return $ C.Ordinary o
sCommentPart (Asterisk)           = return $ C.Asterisk
sCommentPart (At s)               = return $ C.At s
sCommentPart (SpecInComment spec) = do
  specs <- simplifyCBSSpec M.empty M.empty spec
  case specs of 
    [cspec] -> return (C.SpecInComment cspec)
    _       -> throwError "multi-spec in comment"
sCommentPart (CommentTerm t)      = return $ C.CommentTerm t
sCommentPart (CommentPremise f)   = return $ C.CommentPremise f
 
simplifyFSig :: MonadError String m => FSig -> m C.FSig
simplifyFSig (FSig nm ps sort mcs) 
  | null ps                   = return C.FNullary
  | and strictArgs            = return C.FStrict
  | not (or strictArgs)       = return C.FLazy 
  -- checks requirement that only last parameter is variadic, if any
  | any isVariadic (init ps)  = 
      throwError (nm ++ " not a valid variadic funcon")
  | or strictArgs
     , not variadic           = return $ 
        C.FPartiallyLazy (map toStrict strictArgs) Nothing 
  | otherwise {-or strictArgs
     , variadic-}             = return $ 
        C.FPartiallyLazy (map toStrict (init strictArgs)) 
                         (Just $ toStrict (last strictArgs))
  where strictArgs       = map isStrictParam ps
        variadic         = isVariadic (last ps)
        toStrict strict  = if strict then C.Strict else C.Lazy


simplifyFRules :: MonadError String m => Name -> [FRule] -> m ([C.FRewriteRule],[C.FStepRule])
simplifyFRules n rs = partitionEithers <$> mapM (simplifyFRule n) rs


simplifyFRule :: MonadError String m => Name -> FRule -> m (Either C.FRewriteRule C.FStepRule)
simplifyFRule n (FRuleRewrite name mpats rhs conds)
  = do guardM (n == name) ("rule name '" <> name <> "' does not match signature '" <> n <> "'")
       pats <- topLevelFPatterns (maybePattsToPatts mpats)
       rhs' <- case rhs of Nothing -> return Nothing
                           Just t  -> Just <$> simplifyFTerm t
       Left <$> C.FRewriteRule pats rhs' <$> mapM simplifyFSideCondition conds

simplifyFRule n (FRuleStep name st ps_cs)
  = do guardM (n == name) ("rule name '" <> name <> "' does not match signature '" <> n <> "'")
       st'    <- simplifyFStep st
       ps_cs' <- mapM (traverseEither simplifyFPremiseStep simplifyFSideCondition) ps_cs
       guardM (all (== entitiesOfStep st') (map entitiesOfPremiseStep $ lefts ps_cs')) "the entities in a premise must match the entites used in the conclusion"
       return $ Right $ C.FStepRule st' ps_cs'

simplifyFSideCondition :: MonadError String m => FSideCondition -> m C.FSideCondition
simplifyFSideCondition (SCEquality e1 e2)   =
    C.SCEquality <$> simplifyFTerm e1 <*> simplifyFTerm e2
simplifyFSideCondition (SCInequality e1 e2)   =
    C.SCInequality <$> simplifyFTerm e1 <*> simplifyFTerm e2
simplifyFSideCondition (SCPatternMatch e p) =
    C.SCPatternMatch <$> simplifyFTerm e <*> simplifyFPattern p
simplifyFSideCondition (SCIsInSort e ty)    =
    C.SCIsInSort <$> simplifyFTerm e <*> simplifyFTerm ty

simplifyFStep :: MonadError String m => FStep -> m C.FStep
simplifyFStep st
  = do mut  <- uncurry (mergeAssocListsM "mismatched mutable entities in conclusion") (stepMutableEntities st)
       mut' <- mapM simplifyMutableEntity mut
       inp  <- mapM (uncurry simplifyInputEntity) (stepInputEntities st)
       ctrl <- mapM (uncurry simplifyControlEntity) (stepControlEntities st)
       outs <- mapM (uncurry simplifyNameTermPair) (stepOutputEntities st)
       inhs <- mapM (uncurry simplifyNamePatternPair) (stepInheritedEntities st)
       source <- topLevelFPatterns (maybePattsToPatts (stepSource st))
       target <- simplifyFTerm (stepTarget st)
       return $ C.FStep
                 { C.stepSource = source
                 , C.stepTarget = target
                 , C.stepInheritedEntities = inhs
                 , C.stepMutableEntities = mut'
                 , C.stepInputEntities = inp
                 , C.stepOutputEntities = outs
                 , C.stepControlEntities = ctrl
                 }

simplifyFPremiseStep :: MonadError String m => FPremiseStep -> m C.FPremiseStep
simplifyFPremiseStep pst
  = do mut  <- uncurry (mergeAssocListsM "mismatched mutable entities in premise")
                (premiseMutableEntities pst)
       mut' <- mapM simplifyMutableEntityPremise mut
       ctrl <- mapM (uncurry simplifyControlEntityPremise) (premiseControlEntities pst)
       outs <- mapM (uncurry simplifyNamePatternPair) (premiseOutputEntities pst)
       ins  <- mapM (uncurry simplifyInputEntityPremise) (premiseInputEntities pst)
       inhs <- mapM (uncurry simplifyNameTermPair) (premiseInheritedEntities pst)
       source <- simplifyFTerm (premiseSource pst)
       target <- simplifyFPattern (premiseTarget pst)
       return $ C.FPremiseStep
                 { C.premiseSource = source
                 , C.premiseTarget = target
                 , C.premiseInheritedEntities = inhs
                 , C.premiseMutableEntities = mut'
                 , C.premiseInputEntities = ins
                 , C.premiseOutputEntities = outs
                 , C.premiseControlEntities = ctrl
                 }

simplifyMutableEntity :: MonadError String m => (Name, FPattern, FTerm) -> m (Name, C.FPattern, C.FTerm)
simplifyMutableEntity (n,p,t) = (n,,) <$> simplifyFPattern p <*> simplifyFTerm t

simplifyInputEntity :: MonadError String m => Name -> FPattern -> m (Name,[C.FPattern],[MetaVar])
simplifyInputEntity n p = case p of
  PTuple ps -> splitInputPattern ps
  PList ps  -> splitInputPattern ps
  _         -> splitInputPattern [p]
  where 
    takeStarMetaVars :: ([FPattern],[MetaVar]) -> ([FPattern],[MetaVar])
    takeStarMetaVars (PSeqMetaVar mv StarOp : ps', mvs) = 
      takeStarMetaVars (ps',mv:mvs)
    takeStarMetaVars pmvs = pmvs
    splitInputPattern ps = 
      (n,,reverse rmvs) <$> topLevelFPatterns (reverse rps)
      where (rps,rmvs) = takeStarMetaVars (reverse ps,[])

-- special meaning of tuple notation for control entities
simplifyControlEntity :: MonadError String m => Name -> FPattern -> m (Name,Maybe C.FPattern)
simplifyControlEntity n (PTuple [])   = return (n,Nothing)
simplifyControlEntity n t             = (n,) . Just <$> simplifyFPattern t

simplifyMutableEntityPremise :: MonadError String m => (Name, FTerm, FPattern) -> m (Name, C.FTerm, C.FPattern)
simplifyMutableEntityPremise (n,t,p) = (n,,) <$> simplifyFTerm t <*> simplifyFPattern p

-- special meaning of tuple notation for control entities
simplifyControlEntityPremise :: MonadError String m => Name -> FPattern -> m (Name,Maybe C.FPattern)
simplifyControlEntityPremise n (PTuple []) = return (n,Nothing)
simplifyControlEntityPremise n p           = (n,) . Just <$> simplifyFPattern p

simplifyNamePatternPair :: MonadError String m => Name -> FPattern -> m (Name,C.FPattern)
simplifyNamePatternPair n p = (n,) <$> simplifyFPattern p

simplifyInputEntityPremise :: MonadError String m => Name -> FTerm -> m (Name,[C.FTerm],Maybe MetaVar)
simplifyInputEntityPremise n t = case t of
  TList []  -> return (n,[],Nothing)
  TList ts  -> splitInputTerms ts
  TTuple [] -> return (n,[],Nothing)
  TTuple ts -> splitInputTerms ts
  _         -> throwError $ "premise input entity " ++ n ++ " not a list or sequence of terms: " ++ show t
  where splitInputTerms ts = do 
          ts' <- mapM simplifyFTerm ts
          case last ts' of
            C.TVar mv | last mv == '*' -> return (n,init ts',Just mv)
            _                          -> return (n,ts',Nothing)

simplifyNameTermPair :: MonadError String m => Name -> FTerm -> m (Name,C.FTerm)
simplifyNameTermPair n t           = (n,) <$> simplifyFTerm t

topLevelFPatterns :: MonadError String m => [FPattern] -> m [C.FPattern]
topLevelFPatterns xs = concat <$> mapM simplifyFPatterns xs

simplifyFPatterns :: MonadError String m => FPattern -> m [C.FPattern]
simplifyFPatterns (PTuple pats) = concat <$> 
  mapM (\x -> map C.PValue <$> simplify2VPatterns x) pats
simplifyFPatterns p = (:[]) <$> simplifyFPattern p

simplifyFPattern :: MonadError String m => FPattern -> m C.FPattern
simplifyFPattern (PAnnotated pat sort) = C.PAnnotated <$> simplifyFPattern pat
                                                      <*> simplifyFTerm sort
simplifyFPattern PAny             = return C.PWildCard
simplifyFPattern (PMetaVar var)   = return (C.PMetaVar var)
simplifyFPattern (PSeqMetaVar var op) = return (C.PSeqVar var op)
simplifyFPattern vpat                 = C.PValue <$> simplify2VPattern vpat

simplify2VPatterns :: MonadError String m => FPattern -> m [C.VPattern]
simplify2VPatterns (PTuple pats) = concat <$> mapM simplify2VPatterns pats
simplify2VPatterns p = (:[]) <$> simplify2VPattern p

simplify2VPattern :: MonadError String m => FPattern -> m C.VPattern
simplify2VPattern (PTuple pats) = C.PADT "datatype-value" <$> 
  (((C.VPLit (string__ "tuple")):) . concat <$> mapM simplify2VPatterns pats) 
simplify2VPattern (PList pats)  = C.PADT "datatype-value" <$> 
  (((C.VPLit (string__ "list")):) . concat <$> mapM simplify2VPatterns pats)
simplify2VPattern (PADT cons pats) = C.PADT (pack cons) <$> 
  (concat <$> mapM simplify2VPatterns pats)
simplify2VPattern (PLit lit)       = return (C.VPLit (simplifyLiteral lit))
simplify2VPattern (PAnnotated pat sort) = C.VPAnnotated <$> simplify2VPattern pat
                                                        <*> simplifyFTerm sort
simplify2VPattern PAny             = return C.VPWildCard
simplify2VPattern (PMetaVar var)   = return (C.VPMetaVar var)
simplify2VPattern (PSeqMetaVar var op) = return (C.VPSeqVar var op)


simplifyFTerm :: MonadError String m => FTerm -> m C.FTerm
simplifyFTerm (TMetaVar var)        = return $ C.TVar var
simplifyFTerm (TLiteral lit)        = return $ C.TFuncon $ FValue $ simplifyLiteral lit
simplifyFTerm (TName nm)            = return $ C.TName (pack nm)
simplifyFTerm (TApp nm term)        = C.TApp (pack nm) <$> mapM simplifyFTerm term
simplifyFTerm (TTuple terms)        = C.TSeq <$> mapM simplifyFTerm terms
simplifyFTerm (TList terms)         = C.TApp "list" <$> mapM simplifyFTerm terms
simplifyFTerm (TSet terms)         = C.TSet <$> mapM simplifyFTerm terms
simplifyFTerm (TMap terms)         = C.TMap <$> mapM simplifyFTerm terms
simplifyFTerm (TSortUnion t1 t2)    = C.TSortUnion <$> simplifyFTerm t1 <*>
                                                       simplifyFTerm t2
simplifyFTerm (TSortInter t1 t2)    = C.TSortInter <$> simplifyFTerm t1 <*>
                                                       simplifyFTerm t2
simplifyFTerm (TSortComplement t1)  = C.TSortComplement <$> simplifyFTerm t1
simplifyFTerm (TSortSeq t1 op)      = C.TSortSeq <$> simplifyFTerm t1 <*> pure op
simplifyFTerm (TSortComputes term)  = C.TSortComputes <$> simplifyFTerm term
simplifyFTerm (TSortComputesFrom t1 t2) = C.TSortComputesFrom <$> simplifyFTerm t1
                                                              <*> simplifyFTerm t2
simplifyFTerm (TSortPower t1 t2)      = C.TSortPower <$> simplifyFTerm t1 <*> simplifyFTerm t2
simplifyFTerm TAny                  = return C.TAny

--------------------------------------------------------------------

isAppOf :: String -> FTerm -> Bool
isAppOf n (TApp f _) = f == n
isAppOf _ _          = False

isSortSeq :: SeqSortOp -> FTerm -> Bool
isSortSeq op1 (TSortSeq _ op2) = op1 == op2
isSortSeq _   _                = False

abbrvParamPatt :: MonadError String m => FParam -> m C.FPattern
abbrvParamPatt (pp, sorts) = case sorts of
  Just sort | isStrictSort sort -> do 
        sort' <- simplifyFTerm sort
        return $ C.PAnnotated p sort'
  _ ->  return p
  where
    p = case pp of
          PPAny                -> C.PWildCard
          PPMetaVar mvar       -> C.PMetaVar mvar
          PPSeqMetaVar mvar op -> C.PSeqVar mvar op

-- Interpret "f()" as a pattern matching an empty tuple argument
maybePattsToPatts :: Maybe [FPattern] -> [FPattern]
maybePattsToPatts Nothing   = []
maybePattsToPatts (Just []) = [ PTuple [] ]
maybePattsToPatts (Just ps) = ps

entitiesOfStep :: C.FStep -> ([Name],[Name],[Name],[Name],[Name])
entitiesOfStep st = ( map fst (C.stepInheritedEntities st)
                    , map (\(n,_,_) -> n) (C.stepMutableEntities st)
                    , map (\(n,_,_) -> n) (C.stepInputEntities st)
                    , map fst (C.stepOutputEntities st)
                    , map fst (C.stepControlEntities st)
                    )

entitiesOfPremiseStep :: C.FPremiseStep -> ([Name],[Name],[Name],[Name],[Name])
entitiesOfPremiseStep st =
                    ( map fst (C.premiseInheritedEntities st)
                    , map (\(n,_,_) -> n) (C.premiseMutableEntities st)
                    , map (\(n,_,_) -> n) (C.premiseInputEntities st)
                    , map fst (C.premiseOutputEntities st)
                    , map fst (C.premiseControlEntities st)
                    )

--------------------------------------------------------------------

term2tpat :: C.FTerm -> C.TPattern
term2tpat t = case t of 
  C.TSortComputes f         -> C.TPComputes (term2tpat f) 
  C.TSortComputesFrom f t   -> C.TPComputesFrom (term2tpat f) (term2tpat t)
  C.TSortSeq (C.TVar x) op  -> C.TPSeqVar x op
  C.TVar x                  -> C.TPVar x
  C.TAny                    -> C.TPWildCard
  C.TName nm                -> C.TPADT nm []
  C.TApp nm ts              -> C.TPADT nm (map term2tpat ts)
  _                         -> C.TPLit t 
