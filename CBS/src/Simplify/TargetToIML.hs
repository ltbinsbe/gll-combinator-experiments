{-# Language FlexibleContexts, ScopedTypeVariables, FlexibleInstances, 
      TupleSections, OverloadedStrings #-}

module Simplify.TargetToIML where

--------------------------------------------------------------------
import Funcons.EDSL (Values(..), Funcons(FValue), isString_, unString, pat2term, typat2term)
import Types.SourceAbstractSyntax (Name, FLiteral(..), SeqSortOp(..),MetaVar, AliasMap, my_aliases)
import Types.CoreAbstractSyntax (FPattern(..), FTerm(..),
        FSideCondition(..), DataTypeSpec(..),DataTypeAlt(..), 
        EntitySpec(..), ConsSpec(..))
import Types.TargetAbstractSyntax
import Simplify.Utils
import qualified IML.Grammar as RF
import qualified IML.Grammar.Specs as IS
import qualified IML.Trans.ProMan as IML
import IML.Trans.FromFuncons (translate, remVarOp, translate_term)
import qualified Funcons.Operations as VAL
import IML.EDSL
-------------------------------------------------------------------

import Control.Arrow ((***))
import Control.Monad.Trans
import Control.Monad.Writer
import Control.Monad.State
import Data.Text (unpack,pack)
import Data.Map (assocs)
import Data.String (fromString)

import System.IO.Unsafe
trace a b = unsafePerformIO (putStrLn a >> return b)

-- | Type representing value constructors
type VCons = Name
type Cons  = Name

-- | The constructor used for the type-membership predicate
stepR, rewR, tyR :: RF.RSymb
stepR = "->"
rewVR  = "~>"
rewR = "=~="
tyR   = "=ty=>"

rewrite,step :: IsExprs exprs => exprs -> RuleBuilder ()
step = commit stepR
rewrite = commit rewVR
type_member = commit tyR (RF.TVal (VAL.tobool True))

target2iml :: IML.Component CBSFile IS.HighSpec
target2iml = IML.component (\file -> return (execRuleBuilder (gCBSFile file)))

gCBSFile :: CBSFile -> RuleBuilder () 
gCBSFile cbsfile = do
  {- THESE RELATIONS ARE NOW DECLARED IN main.iml
  rel_decl stepR [{-IS.Repeatable-}]
  rel_decl rewR [{-IS.Repeatable-}]
  rel_decl tyR []  -- type-member relation
  -}
  mapM_ (gCBSSpec (aliases cbsfile)) (cbs cbsfile)

  {- THESE RULES ARE NOW SPECIFIED IN main.iml FILE 
  -- fall back rule for type-membership
  --   that checks whether first argument is a value
  [v1,v2,v3] <- mapM (const fresh_var) [1..3]
  lhs (RF.PCons ty_cons [RF.PVar v1, RF.PVar v2])
  gRewrite (RF.TVar v1) (RF.PVar v3)
  gRewrite (RF.TVar v2) (RF.PCons "values" [])
  is_terminating stepR (RF.TVar v3)
  commit tyR (RF.TVal (VAL.tobool True))
  -- fall back rule that determines non-membership
  [v1,v2,v3,v4,v5] <- mapM (const fresh_var) [1..5]
  lhs (RF.PCons ty_cons [RF.PVar v1, RF.PVar v2])
  gRewrite (RF.TVar v1) (RF.PVar v3)
  gRewrite (RF.TVar v2) (RF.PVar v4)
  pm (vop "type-member" [RF.TVar v3, RF.TVar v4]) (RF.PVar v5)
  commit_prio 0 tyR (RF.TVar v5)
  -}

gCBSSpec  :: AliasMap -> CBSSpec -> RuleBuilder ()
gCBSSpec am (FunconSpec spec)    = gFSpecWithMP_Aliases am spec
gCBSSpec am (DataTypeSpec spec)  = gData_Aliases am spec
gCBSSpec am (MetaSpec _)         = return ()
gCBSSpec am (EntitySpec spec)    = gEntitySpec spec
gCBSSpec am (ConsSpec spec)      = gCons_Aliases am spec

gEntitySpec :: EntitySpec -> RuleBuilder ()
gEntitySpec spec = case spec of 
  InheritedSpec n t -> ent_decl n (tTermAsExpr t)
  MutableSpec n t   -> ent_decl n (tTermAsExpr t)
  OutputSpec n      -> ent_decl n (RF.ETerm (RF.TVal (VAL.ADTVal "list" [])))
  InputSpec n       -> ent_decl n (RF.ETerm (RF.TVal (VAL.ADTVal "list" [])))
  ControlSpec n     -> ent_decl n (RF.ETerm (RF.TVal (VAL.none__))) >>
                         term_eid n (Right "some") 

gFSpecWithMP_Aliases :: AliasMap -> FunconSpec -> RuleBuilder()
gFSpecWithMP_Aliases am (FRules nm a b c d) = 
  forM_ (my_aliases nm am) (\nm' -> gFSpecWithMP (FRules nm' a b c d)) 
 
gFSpecWithMP :: FunconSpec -> RuleBuilder () 
gFSpecWithMP spec@(FRules nm sig _ _ _) = gFSpec spec >> 
  -- rules for meta-programming
  astFuncons nm (Just 2)
 where  
    gFSpec (FRules nm sig _ rs ss) = do 
      mapM_ (gRewriteRule nm) rs
      mapM_ (gStepRule nm) ss

gRewriteRule :: Name -> FRewriteRule -> RuleBuilder () 
gRewriteRule nm (FRewriteRule source target bar) = do
  pats <- mapM tFPattern source
  lhs (RF.PCons nm pats)
  mapM gSideCond bar
  rewrite $ case target of Nothing -> map RF.ETerm $ tTerm2Seq (TName "null")
                           Just t  -> map RF.ETerm $ tTerm2Seq t 
gStepRule :: Name -> FStepRule -> RuleBuilder ()
gStepRule nm (FStepRule fstep bar) = do
  pats <- mapM tFPattern (stepSource fstep) 
  lhs (RF.PCons nm pats)
  -- inherited entities
  ro_vars <- mapM gROvar (stepInheritedEntities fstep)
  mapM_ (\(n, v) -> acc n (RF.PVar v) >> up n (RF.TVar v)) ro_vars
  -- mutable entities (IN)
  forM (stepMutableEntities fstep) $ \(n,p,t) -> do
    tFPattern p >>= acc n
  -- TODO: input entities
  -- * The "rest" of the input must be bound by a meta-var so that
  --    the first premise can provide this as additional input
--  forM (stepInputEntities fstep) $ \(n, vars) ->  
--    acc n =<< tListPattern (map PMetaVar vars)

  gConditions bar
  -- control entities
  forM (stepControlEntities fstep) $ \(n, mt) -> 
    acc n (RF.PVal (VAL.none__)) >> 
    case mt of 
      Nothing   -> up n (RF.TVal (VAL.none__))
      Just t    -> rewAndPut n (TApp "some" [pat2term t])
  -- mutable entities (OUT)
  forM (stepMutableEntities fstep) $ \(n,p,t) -> do
    rewAndPut n t 
  -- output entities
  forM (stepOutputEntities fstep) $ \(n, t) -> do
    var1 <- fresh_var
    acc n (RF.PVar var1)
    var2 <- fresh_var 
    gRewriteToVal [RF.TCons "list-append" [RF.TVar var1 
                                          ,RF.TCons "list-singleton" (tTerm2Seq t)]]
                  [RF.PVar var2]
    up n (RF.TVar var2)
  step (tTerm2Seq (stepTarget fstep))
--  ros <- let op (n,p) = (n,) <$> tPattern p
--          in mapM op (stepInheritedEntities fstep)     --acc  
--  rws <- mapM rewriteMutVal (stepMutableEntities fstep)
--  wos1 <- mapM (uncurry rewriteOutVal) (stepOutputEntities fstep)
--  wos2 <- mapM (uncurry rewriteConVal) (stepControlEntities fstep)
--  let conditions = --concatMap (map Left . fst) wos1 ++
                   --concatMap (map Left . fst) rws  ++
                   --concatMap (map Left . fst) wos2 ++ 
  where gROvar (n,p) = case p of 
          PMetaVar var  -> return (n, var)
          PWildCard     -> (n,) <$> fresh_var
          _             -> do var <- fresh_var
                              gSideCond (SCPatternMatch (TVar var) p)
                              return (n, var)
        rewAndPut n t             = do  var <- fresh_var 
                                        gRewriteToVal (tTerm2Seq t) [RF.PVar var]
                                        up n (RF.TVar var)

gConditions :: [Either FPremiseStep FSideCondition] -> RuleBuilder () 
gConditions cs = mapM_ (mapeither gPremise gSideCond) cs
  where mapeither f _ (Left e)  = f e
        mapeither _ f (Right e) = f e

gPremise :: FPremiseStep -> RuleBuilder ()
gPremise pstep = do 
  target' <- tFPattern (premiseTarget pstep)
  let source' = tTerm2Seq (premiseSource pstep)
  var <- fresh_var 
  gOptRewrite source' [RF.PVar var]
  -- inherited entities 
  inhI <- forM (premiseInheritedEntities pstep) $ \(n,t) -> do
            var <- fresh_var 
            gRewriteToVal (tTerm2Seq t) [RF.PVar var]
            return (n, RF.ETerm $ RF.TVar var)
               
  let inhO = map (id *** (const (RF.PAny))) (premiseInheritedEntities pstep)
  -- mutable entities
  mutI <- forM (premiseMutableEntities pstep) $ \(n,t,p) -> do
            var <- fresh_var 
            gRewriteToVal (tTerm2Seq t) [RF.PVar var]
            return (n,RF.ETerm (RF.TVar var))
  mutO <- mapM (\(n,t,p) -> (n,) <$> tFPattern p)
                  (premiseMutableEntities pstep)
  -- output entities
  let outI = map (\(n,_) -> (n, RF.ETerm (RF.TVal (VAL.ADTVal "list" []))))
                              (premiseOutputEntities pstep)
  let matchOutList n p = case p of
        (PValue (PADT "list" ps))  -> (n,) <$> tListPattern (map PValue ps) -- TODO pattern matching lists currently not supported, requires usage of destructors like `head` and `tail`
        _         -> error "premise output not formed by a list of patterns"
  outO <- mapM (uncurry matchOutList) (premiseOutputEntities pstep)
  -- control entities
  let ctrlI = map (\(n,_) -> (n, RF.ETerm (RF.TVal (VAL.none__)))) 
                  (premiseControlEntities pstep)
  ctrlO <- forM (premiseControlEntities pstep) $ \(n,mp) -> case mp of 
            Just p  -> (n,) . RF.PVal . VAL.some__ <$> tFPattern p
            Nothing -> return (n, RF.PVal VAL.none__)
  -- TODO: input entities 
   --ExtraInput determines that there is `other` input than provided by the terms
   -- this input is the `left over' from the conclusion (or last premise?)
  {-
  inpI <- forM (premiseInputEntities pstep) $ \(n,vars,_) -> do
    var <- fresh_var
    gRewriteExpr (vop "list" (map tTerm vars)) (RF.PVar var)
    return (n, RF.TVar var)-}
  -- Check whether all provided input has been consumed.
  -- If ExtraInput than more may be consumed
  -- If ExactInput than inpO must be equal to []
  {- let inpO = map (\(n,_,access) -> -}
--  woaccs  <- let  op (n,p) = (n,) <$> tPattern p
--                  opm (n,Nothing) = (n++"-nothing",) . RF.PVar <$> IML.fresh_var_
--                  opm (n,Just p)  = op (n,p) 
--             in (++) <$> mapM op (premiseOutputEntities pstep)
--                     <*> mapM opm (premiseControlEntities pstep)
--  inhs <- mapM (uncurry rewriteOutVal) (premiseInheritedEntities pstep)
--  muts <- mapM rewriteMutVal (premiseMutableEntities pstep)
--  let roups   = map snd inhs
--      rwups   = map snd muts
  let ins  = map (id *** (:[])) $ inhI ++ mutI ++ outI ++ ctrlI -- ++ inpI
      outs = map (id *** (:[])) $ inhO ++ mutO ++ outO ++ ctrlO -- ++ inpO
--  v <- IML.fresh_var_
  premise (RF.TConf [RF.ETerm (RF.TVar var)] ins) stepR (RF.PConf [target'] outs)
--  return -- $ (concatMap fst inhs) ++  (concatMap fst muts) ++
  --        [RF.Prem [] (RF.TConf (RF.ETerm source') ins) stepRel
    --                  (RF.PConf target' outs)]
--        [gRewrite source' v
--        ,RF.Prem (RF.TVar v) (RF.sRel stepR) target' roups rwups woaccs]

tListPattern :: [FPattern] -> RuleBuilder RF.Pattern
tListPattern ps = RF.PVal . VAL.ADTVal "list" <$> mapM tFPattern ps
{-foldM attach (RF.PCons nil_v []) . reverse
  where attach acc p = do pat <- tPattern p
                          return (RF.PCons "cons" [pat, acc])-}

gSideCond :: FSideCondition -> RuleBuilder () 
gSideCond sc = 
  case sc of
    SCEquality t1 t2        -> mkEquality t1 t2 truePat 
    SCInequality t1 t2      -> mkEquality t1 t2 falsePat
    SCIsInSort t1 sort      -> case sort of 
      TSortComplement sort' -> mkSort t1 sort' falsePat
      _                     -> mkSort t1 sort truePat
    SCNotInSort t1 sort     -> mkSort t1 sort falsePat
    SCPatternMatch t p      -> do
      p' <- tFPattern p 
      gOptRewriteExpr (map RF.ETerm $ tTerm2Seq t) [p']
  where mkEquality t1 t2 b = do
          v1    <- fresh_var
          gRewriteToVal (tTerm2Seq t1) [RF.PVar v1]
          v2    <- fresh_var
          gRewriteToVal (tTerm2Seq t2) [RF.PVar v2]
          pm (vop "is-equal" [RF.TVar v1, RF.TVar v2]) b
{-        mkSort (TVar v1) sort b 
            | let mop = last v1, mop == '*' || mop == '?' || mop == '+' = 
              let tup = TTuple [TVar v1]
                  seqs = TApp "tyseq" (TTuple [sort, TFuncon (FValue (String [mop]))])
              in mkSort tup seqs b-}
        mkSort t1 sort b = 
          tycheck t1' sort' b --rewriting performed in rules for tychecking
         where (t1',sort') = (tTerm2Seq t1, tTerm sort)  
    
tycheck :: [RF.Term] -> RF.Term -> RF.Pattern -> RuleBuilder ()
tycheck vals ty b = premise (ty : vals) (mRel tyR) b

lit2Val :: VAL.HasValues t => FLiteral -> VAL.Values t 
lit2Val lit = case lit of
  FLiteralNat nat   -> VAL.Nat (toInteger nat)
  FLiteralFloat f   -> VAL.Float f 
  FLiteralString s  -> fromString s
  FLiteralAtom c    -> fromString c


-- | Assuming no other patterns than the conclusions' left-hand side
-- have annotation. For other patterns it is safe to use `tPattern`
tFPattern :: FPattern -> RuleBuilder RF.Pattern
tFPattern (PValue vpat) = tVPattern vpat
tFPattern (PAnnotated PWildCard sort) = do
  v <- fresh_var
  tFPattern (PAnnotated (PMetaVar v) sort)
tFPattern (PAnnotated (PMetaVar v) sort) = do
  add_var_decl_ (gVarDecl v Nothing (Just sort))
  return (RF.PVar v)
tFPattern (PAnnotated (PSeqVar v op) sort) 
 | v == "___" = fresh_var >>= \v' -> tFPattern (PAnnotated (PSeqVar v' op) sort)
 | otherwise  = do
    add_var_decl_ (gVarDecl (remVarOp v) (Just op) (Just sort))
    return (RF.PVar (remVarOp v))
tFPattern (PAnnotated p v) = error "unexpected annotation"
tFPattern (PMetaVar var) = return $ RF.PVar var
tFPattern (PSeqVar var op)
 | var == "___" = fresh_var >>= \v' -> tFPattern (PSeqVar v' op)
 | otherwise    = do
  add_var_decl_ (gVarDecl (remVarOp var) (Just op) Nothing)
  return $ RF.PVar (remVarOp var)
tFPattern PWildCard = RF.PVar <$> fresh_var

tVPattern :: VPattern -> RuleBuilder RF.Pattern
tVPattern (VPAnnotated VPWildCard sort) = do
  v <- fresh_var
  tVPattern (VPAnnotated (VPMetaVar v) sort)
tVPattern (VPAnnotated (VPMetaVar v) sort) = do
  add_var_decl_ (gVarDecl v Nothing (Just sort))
  return (RF.PVar v)
tVPattern (VPAnnotated (VPSeqVar v op) sort) 
 | v == "___" = fresh_var >>= \v' -> tVPattern (VPAnnotated (VPSeqVar v' op) sort) 
 | otherwise  = do
  add_var_decl_ (gVarDecl (remVarOp v) (Just op) (Just sort))
  return (RF.PVar (remVarOp v))
tVPattern (VPAnnotated p v) = error "unexpected annotation"
tVPattern (PADT cons ps)
   -- TODO: generate variable with conditions that say that :
    -- a) the matched value has `adt-constructor` equal to `string__ cons`
    -- b) the matched value has `adt-fields` that match the patterns `ps`
 | cons == "datatype-value", not (null ps) = do
    p' <-  tVPattern (head ps)
    ps' <- mapM tVPattern (tail ps)
    var_rewrite <- fresh_var
    var <- fresh_var
    gRewriteToVal [RF.TVar var_rewrite] [RF.PVar var] 
    let consPrem = RF.Prem []   (RF.TConf [RF.VOP "adt-constructor" [RF.ETerm $ RF.TVar var]] [])
                    (sRel rewR) (RF.PConf [p'] [])
    let valsPrem = RF.Prem []   (RF.TConf [RF.ETerm $ RF.TCons "list-elements" [RF.TCons "adt-fields" [RF.TVar var]]] [])
                    (sRel rewR) (RF.PConf ps' [])
    add_var_decl_ (RF.VarDecl var 1 (Just 1) RF.Shortest [Left consPrem, Left valsPrem])
    return (RF.PVar var_rewrite)
 | otherwise = do
    v <- fresh_var 
    pat' <- RF.PVal . VAL.ADTVal cons <$> mapM tVPattern ps
    let rewPrem = Left $ RF.Prem [] (toTConf (RF.TVar v)) (sRel rewR)
                                    (toPConf pat')
    add_var_decl_ (RF.VarDecl v 1 (Just 1) RF.Longest [rewPrem])
    return (RF.PVar v)
tVPattern VPWildCard = RF.PVar <$> fresh_var
tVPattern (VPMetaVar var) = return $ RF.PVar var
tVPattern (VPSeqVar var op)
 | var == "___" = fresh_var >>= \v' -> tVPattern (VPSeqVar v' op)
 | otherwise    = do
  add_var_decl_ (gVarDecl (remVarOp var) (Just op) Nothing)
  return $ RF.PVar (remVarOp var)
tVPattern (VPLit lit)  = return $ RF.PVal (VAL.vmap (RF.term2pattern . translate) lit)
tVPattern (VPType tpat) = tTPattern tpat

tTPattern :: TPattern -> RuleBuilder RF.Pattern
tTPattern TPWildCard = RF.PVar <$> fresh_var
tTPattern (TPVar var) = return $ RF.PVar var
tTPattern (TPSeqVar var op) 
 | var == "___" = fresh_var >>= \v' -> tTPattern (TPSeqVar v' op)
 | otherwise    =  do
  add_var_decl_ (gVarDecl (remVarOp var) (Just op) Nothing)
  return $ RF.PVar (remVarOp var)
tTPattern (TPLit fterm) = error "missing translation for type-literals"
tTPattern (TPComputes p) = tTPattern p 
tTPattern (TPComputesFrom _ p) = tTPattern p 
tTPattern (TPADT cons ps) = RF.PVal . VAL.ComputationType . VAL.Type . VAL.ADT cons <$> mapM tTPattern ps 

tTerms :: [FTerm] ->  [RF.Term]
tTerms = map tTerm

tTermAsExpr :: FTerm -> RF.Expr
tTermAsExpr (TName nm)    = RF.VOP (unpack nm) [] 
tTermAsExpr (TApp nm ts)  = RF.VOP (unpack nm) (map tTermAsExpr ts)
tTermAsExpr t             = RF.ETerm (tTerm t)

tTerm2Seq :: FTerm -> [RF.Term]
tTerm2Seq (TSeq ts) = concatMap tTerm2Seq ts
tTerm2Seq t         = [tTerm t]

tTerm :: FTerm -> RF.Term
tTerm = translate_term

{-
tFuncons :: [Funcons] -> [RF.Term]
tFuncons = map tFuncon 

tFuncon :: Funcons -> RF.Term
tFuncon (FName nm)     = RF.TCons False (unpack nm) []
tFuncon (FApp nm f)    = RF.TCons False (unpack nm) $ case f of 
                            FTuple ts -> tFuncons ts
                            _         -> [tFuncon f]
tFuncon (FTuple fs)    = RF.TCons False "tuple" (tFuncons fs)
tFuncon (FList fs)     = RF.TCons False "list" (tFuncons fs)
tFuncon (FSet fs)      = RF.TCons False "set" (tFuncons fs)
tFuncon (FMap fs)      = RF.TCons False "map" (tFuncons fs)
tFuncon (FValue v)     = trace "warning: missing value translations"
  $ RF.TCons True "some-value" []
tFuncon _ = error "missing Funcons translation"
-}

gVarDecl :: RF.MVar -> Maybe SeqSortOp -> Maybe FTerm -> RF.VarDecl
gVarDecl x mop msort = RF.VarDecl x lb mub strat tycheck
  where (tycheck,strat) = case msort of 
          Nothing -> ([], RF.Shortest)
          Just sort -> ([Left (RF.Prem [] 
                         (toTConf (ty'++ [RF.TVar x])) (mRel tyR) (toPConf res))]
                       ,RF.Longest)
            where (ty',res) = case sort of 
                      TSortComplement sort' -> (tTerm2Seq sort', falsePat)
                      _                     -> (tTerm2Seq sort, truePat)
        (lb,mub) = case mop of  Just StarOp -> (0, Nothing)
                                Just PlusOp -> (1, Nothing)
                                Just QuestionMarkOp -> (0, Just 1)
                                Nothing     -> (1, Just 1)

gRewriteToValExpr :: [RF.Expr] -> [RF.Pattern] -> RuleBuilder ()
gRewriteToValExpr expr pat = premise expr (mRel rewVR) pat

gOptRewriteExpr :: [RF.Expr] -> [RF.Pattern] -> RuleBuilder ()
gOptRewriteExpr expr pat = premise expr (sRel rewR) pat


gRewriteToVal :: [RF.Term] -> [RF.Pattern] -> RuleBuilder ()
gRewriteToVal term = gRewriteToValExpr (map RF.ETerm term) 

gOptRewrite :: [RF.Term] -> [RF.Pattern] -> RuleBuilder ()
gOptRewrite term = gOptRewriteExpr (map RF.ETerm term)

truePat, falsePat :: RF.Pattern
truePat  = RF.PVal (VAL.tobool True)
falsePat = RF.PVal (VAL.tobool False)
 
gData_Aliases :: AliasMap -> DataTypeSpec -> RuleBuilder ()
gData_Aliases am (DataTypeDecl nm tyargs alts) = 
  forM_ (my_aliases nm am) (\nm' -> gData (DataTypeDecl nm' tyargs alts))
      
gData :: DataTypeSpec -> RuleBuilder ()
gData d@(DataTypeDecl nm tyargs alts) = do
  -- generate rules for inclusion constructors
  gAlts d
  --term_pc stepR (Right $ toVCons nm)
  --term_pc rewVR (Right $ toVCons nm) 
  -- axiom for type
  (vars,typats) <- unzip <$> mapM mkPat tyargs
  pats <- mapM tTPattern typats
  lhs (RF.PCons nm pats)
  vars' <- forM vars $ \var -> do
            var' <- fresh_var
            gRewriteToVal [RF.TVar var] [RF.PVar var']
            return var' -- TODO share these rewrites with sidecons in bar1
  rewrite (vop "adt-type" (RF.TVal (fromString nm) : (map RF.TVar vars'))) --rewrite
  -- congruence rules
  strictFCongs nm
  -- type alternative for type -- no longer required since ADT-builtin
  --typeMemberAltCons "types" [] nm (map snd tyargs)
  astFuncons nm (Just $ length pats) -- meta-funcons for type
  where mkPat :: TPattern -> RuleBuilder (MetaVar, TPattern)
        mkPat tpat =  case tpat of
          TPVar var       -> return (var, tpat)
          TPSeqVar var op -> return (remVarOp var, tpat)
          TPWildCard      -> do var <- fresh_var
                                return (var, TPVar var)
          _               -> error "unexpected type-parameter pattern"

gAlts :: DataTypeSpec -> RuleBuilder ()
gAlts dt@(DataTypeDecl _ _ alts) = mapM_ (gAlt dt) alts

gAlt :: DataTypeSpec -> DataTypeAlt -> RuleBuilder () 
gAlt (DataTypeDecl tyname tyargs _) alt = case alt of
  DataTypeInclusion sort      -> 
    typeMemberAltIncl tyname tyargs sort

gCons_Aliases :: AliasMap -> ConsSpec -> RuleBuilder ()
gCons_Aliases am (ValCons nm a b tynm d) = 
  forM_ (my_aliases nm am) (\nm' -> 
    forM_ (my_aliases tynm am) (\tynm' -> gCons (ValCons nm' a b tynm' d)))

gCons :: ConsSpec -> RuleBuilder()
-- SIMPLIFICATION: all constructors are strict
gCons (ValCons nm _ argstys tynm typats) = do
--    gDataTypeValue nm -- rules for the operational behaviour of cons
    typeMemberAltCons tynm typats nm argstys -- type-membership rule
    astFuncons nm (Just nr_args)
  where nr_args = length argstys 


{-  DataTypeMemberConstructor nm' args mtyargs -> do
    --term_pc stepR (Right $ toVCons nm)
    --term_pc rewVR (Right $ toVCons nm)
    gDataTypeValue (length args) nm         -- rules for the operational behaviour of cons
    typeMemberAltCons tyname (maybe tyargs id mtyargs) nm args -- type-membership rule
    astFuncons nm (length args)
  where nm = unpack nm'
-}

typeMemberAltIncl :: Name -> [TPattern] -> FTerm -> RuleBuilder () 
typeMemberAltIncl tyname tyargs sort = do
  v1 <- fresh_var
  typats <- mapM tTPattern tyargs 
  lhs [RF.PVal (adt_type (pack tyname) typats), RF.PVar v1]
  gSideCond (SCIsInSort (TVar v1) sort)
  type_member 

typeMemberAltCons :: Name -> [TPattern] -> Name -> [FTerm] -> RuleBuilder ()
typeMemberAltCons tyname tyargs nm sorts = do
  typats <- mapM tTPattern tyargs 
  patvars <- forM sorts $ \sort -> do
    -- TODO extend the `sorts` argument to contain information about the variable
    --   in order to avoid generating sequence-variables where not necessary
    var <- fresh_var 
    case mkSort sort of 
      Nothing         -> do
        gSideCond (SCIsInSort (TVar var) sort)
        return (var, sort)
      Just (sort',op) -> do 
        add_var_decl_ (gVarDecl var (Just op) (Just (TSortSeq sort' op)))
        return (var, sort)
  lhs [RF.PVal (adt_type (pack tyname) typats)
      ,RF.PVal (adt (pack nm) (map (RF.PVar . fst) patvars))]
  type_member 
  where mkSort t = case t of 
          TSortSeq t' op  -> Just (t', op)
          TVar var        -> case last var of
              '*'         -> Just (t, StarOp)
              '?'         -> Just (t, QuestionMarkOp)
              '+'         -> Just (t, PlusOp)
              _           -> Nothing
          _               -> Nothing 

gDataTypeValue :: Cons -> RuleBuilder ()
gDataTypeValue cs =  do -- build axiom
  var  <- fresh_var
  lhs (RF.PCons cs [RF.PVar var])
  add_var_decl_ (gVarDecl var (Just StarOp) (Just (TName "values")))
  rewrite (RF.TCons "datatype-value" (RF.TVal (fromString cs) : [RF.TVar var])) --rewrite
  strictFCongs cs   -- build congruences

strictFCongs :: Cons -> RuleBuilder ()
strictFCongs cs = do
  vs_var  <- fresh_var
  x_var   <- fresh_var
  x_var_rw<- fresh_var
  x_var'  <- fresh_var
  ys_var  <- fresh_var
  lhs (RF.PCons cs [RF.PVar vs_var, RF.PVar x_var, RF.PVar ys_var])
  add_var_decl_ (gVarDecl vs_var (Just StarOp) (Just (TName "values")))
  add_var_decl_ (gVarDecl ys_var (Just StarOp) Nothing)
  gOptRewrite [RF.TVar x_var] [RF.PVar x_var_rw]
  premise (RF.TVar x_var_rw) (sRel stepR) (RF.PVar x_var')
  commit (sRel stepR) (RF.TCons cs [RF.TVar vs_var, RF.TVar x_var', RF.TVar ys_var])
 
mkValOpRules :: [RF.Rule]
mkValOpRules = rules
  where IS.Spec new = execRuleBuilder $ mapM_ (uncurry mkrule) 
                                   $ assocs (VAL.library :: VAL.Library RF.Term)
        (_,_,_,_,rules) = IS.partition_decls new

        mkrule :: VAL.OP {- String, operation name -} -> VAL.ValueOp t -> RuleBuilder ()
        mkrule nm op = case op of 
            VAL.NullaryExpr _  -> build $ Just 0 
            VAL.UnaryExpr _    -> build $ Just 1
            VAL.BinaryExpr _   -> build $ Just 2
            VAL.TernaryExpr _  -> build $ Just 3
            VAL.NaryExpr _     -> build Nothing
         where
          build marity = do 
            strictFCongs nm -- congruence rules
            mkAxiom -- axiom
            astFuncons nm marity --ast-* funcons
            where mkAxiom = case marity of 
                    Just arity -> do
                      vars <- mapM (const fresh_var) [1..arity]
                      lhs (RF.PCons nm (map RF.PVar vars))
                      vars' <- forM vars $ \var -> do -- termination side conditions
                        var' <- fresh_var 
                        gSideCond (SCPatternMatch (TVar var) (PMetaVar var'))
                        is_terminating stepR (RF.TVar var')
                        return var'
                      rewrite (vop nm (map RF.TVar vars'))
                    Nothing -> do
                      var <- fresh_var
                      lhs (RF.PCons nm [RF.PVar var])
                      var' <- fresh_var
                      add_var_decl_ (gVarDecl var (Just StarOp) Nothing)
                      add_var_decl_ (gVarDecl var' (Just StarOp) Nothing)
                      gOptRewrite [RF.TVar var] [RF.PVar var'] 
                      is_terminating stepR (RF.TVar var')
                      rewrite (vop nm [RF.TVar var'])
  

-- meta-programming specific stuff

ctR, dlR, ulR :: RF.RSymb
ctR = "=ct=>"
dlR = "=dl=>"
ulR = "=ul=>"

ctRelRule :: Name -> RuleBuilder ()
ctRelRule nm = do
  var <- fresh_var
  var' <- fresh_var
  lhs (RF.PCons nm [RF.PVar var])
  var_decl var  0 Nothing RF.Longest []
  var_decl var' 0 Nothing RF.Longest []
  premise (RF.TVar var) ctR (RF.PVar var')
  commit ctR (RF.TCons nm [RF.TVar var'])

dlRelRule :: Name -> RuleBuilder ()
dlRelRule nm = do
  var <- fresh_var
  var' <- fresh_var
  lhs (RF.PVal (VAL.ADTVal (pack astv_nm) [RF.PVar var]))
  var_decl var  0 Nothing RF.Longest []
  var_decl var' 0 Nothing RF.Longest []
  premise (RF.TVar var) dlR (RF.PVar var')
  commit dlR (RF.TCons nm [RF.TVar var'])
  where astv_nm = "astv-" ++ nm

ulRelRule :: Name -> RuleBuilder ()
ulRelRule nm = do
  var <- fresh_var
  var' <- fresh_var
  lhs (RF.PCons nm [RF.PVar var])
  var_decl var  0 Nothing RF.Longest []
  var_decl var' 0 Nothing RF.Longest []
  premise (RF.TVar var) ulR (RF.PVar var')
  commit ulR (RF.TCons astv_nm [RF.TVar var'])
  where astv_nm = "astv-" ++ nm 

promoteRule :: Name -> RuleBuilder ()
promoteRule nm = do
  var <- fresh_var
  lhs (RF.PCons nm [RF.PVar var])
  commit ulR (RF.TCons "astv-promote" [RF.TCons nm [RF.TVar var]])

--
-- 1 Generate funcon for funcon named, say "scope", with arity 2
--   > value constructor astv-scope with congruence rules
-- 2 Termination for value constructor
-- 3 Rule that types astv-scope(A:asts,B:asts) as asts
-- 4 astv-scope(A,B) =dl=> scope(Ac, Bc)
-- 5 scope(Ac,Bc) =ul=> astv-scope(A,B)
-- 6 astv-scope(A,B) =ct=> astv-scope(A,B)
-- 7 astv-scope(A,B) =ul=> astv-promote(astv-scope(A,B))
astFuncons :: Name -> Maybe Int -> RuleBuilder()
astFuncons nm marity = return () {-do
  ctRelRule nm
  --term_pc stepR (Right $ "astv-" ++ nm)     -- 2
  --term_pc rewR  (Right $ "astv-" ++ nm)     -- 2
  gDataTypeValue astv_nm                  -- 1a
  typeMemberAltCons "asts" [] astv_nm [TSortSeq (TName "asts") StarOp] --3
  dlRelRule nm                              -- 4 
  ulRelRule nm                              -- 5
  ctRelRule astv_nm                         -- 6
  promoteRule astv_nm
  where astv_nm = "astv-" ++ nm
-}
