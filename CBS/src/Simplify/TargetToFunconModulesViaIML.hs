{-# Language FlexibleContexts, ScopedTypeVariables, LambdaCase
        , MultiParamTypeClasses, TupleSections, FlexibleInstances #-}

module Simplify.TargetToFunconModulesViaIML where

--------------------------------------------------------------------
import Funcons.EDSL (Funcons(FValue))
import Types.SourceAbstractSyntax (SeqSortOp(..), FLiteral(..))
import Types.CoreAbstractSyntax (FPattern(..), FTerm(..),FSideCondition(..))
import Types.TargetAbstractSyntax
import Simplify.TargetToIML hiding (tPatterns, tPattern, tTerm, tMVar, tAnn)
import Control.Arrow
import Data.Text (pack)
import qualified Types.FunconModule as F
import qualified IML.Grammar.RuleFormat as RF
import qualified IML.Grammar.Grammar as LOW
import qualified IML.Tools as IML
import IML.Trans.Bindings
import IML.Trans.ToGraph
import IML.Trans.FromGraph
import IML.Trans.ToLower
import IML.Trans.ReorderFactor hiding (schedule)
import IML.Trans.LeftFactor
import IML.Trans.Sanitise
import Types.Sequentialisation

-- required for printing generated statements
import Data.Functor.Identity
import Data.List (intersperse)
import System.IO.Unsafe
import IML.Printer (ppStmts)
import Text.PrettyPrint.HughesPJ
--------------------------------------------------------------------

target2fmodule :: IML.Component CBSFile F.FunconModule
target2fmodule = IML.component simplifyCBSFile

simplifyCBSFile :: CBSFile -> IML.ProMan F.FunconModule
simplifyCBSFile cbsfile = do 
    fspecs <- mapM simplifyFunconSpec (funcons cbsfile)
    return (F.FunconModule fspecs (entities cbsfile) (datatypes cbsfile))

simplifyFunconSpec :: FunconSpec -> IML.ProMan F.FunconSpec
simplifyFunconSpec (FRules nm sig mdoc rewrites steps) = do
    rewrites'   <- mapM ((gRuleBody rtab =<<) . tRewriteRule nm) rewrites
    steps'      <- mapM ((gRuleBody rtab =<<) . tStepRule nm) steps
    rewrites''  <- simplifyRules rewrites'  
    steps''     <- simplifyRules steps'
    rstmts      <- mapM genRewrites rewrites''
    sstmts      <- mapM genSteps steps''
    unsafePerformIO (writeFile ("/tmp/" ++ nm ++ ".stmts") 
     (printStmts (rewrites' ++ steps' ++ rewrites'' ++ steps'')))
       `seq` return (F.FunconSpec nm sig mdoc rstmts sstmts) 
  where rtab = RF.relInsert "~>" 0 [RF.IsPure] RF.relEmpty

simplifyRules :: [LOW.Stmts] -> IML.ProMan [LOW.Stmts]
simplifyRules [] = return []
simplifyRules rs = runIdentity <$> IML.runComponent paper5 (Identity rs)
  where chain0,chain1,chain2,chain3,chain4 :: 
          Traversable f => IML.Component (f [LOW.Stmts]) (f [LOW.Stmts])
        chain0 = check_bindings >>> graphify >>> sequentialise
        chain1 = check_bindings >>> left_eq_factor >>> reorder
        chain2 = check_bindings >>> left_factor
        chain3 = check_bindings >>> graphify >>> reorder_factor 
        chain4 = check_bindings >>> graphify >>> sequentialise >>> remove_rebindings 
                                >>> graphify >>> reorder_factor
                                >>> reorder  >>> remove_common_rewrites

        -- pipelines used in the paper
        paper1,paper1b,paper2,paper3,paper4,paper5 :: 
          Traversable f => IML.Component (f [LOW.Stmts]) (f [LOW.Stmts])
        paper1 = check_bindings
        paper1b = check_bindings >>> graphify >>> sequentialise
        paper2 = check_bindings --handle-thrown reordered branches
        paper3 = check_bindings >>> reorder 
        paper4 = check_bindings >>> left_factor 
        paper5 = check_bindings >>> graphify >>> reorder_factor

genRewrites :: LOW.Stmts -> IML.ProMan [F.FRewriteStmt]
genRewrites ss = concat <$> mapM gR ss

gR :: LOW.Stmt -> IML.ProMan [F.FRewriteStmt]
gR (LOW.Branches sss) = (:[]) . F.RBranches <$> mapM genRewrites sss
gR (LOW.PM_Args ps)   = return [F.ArgsPattern F.fargs_var (tPatterns ps)]
gR (LOW.PM e p)       = return $ (:[]) $ F.CheckSideCondition $ case e of
  RF.VOP "type-member" [e1,e2] -> case e1 of 
      (RF.Val (RF.TVar (RF.MVar v l mu))) | l /= 1, 1 /= maybe 2 id mu 
        -> scSeqElemsInSort v (expr2term e2)
      _ -> scIsInSort (expr2term e1) (expr2term e2)
    where (scSeqElemsInSort,scIsInSort) = case p of 
            RF.PCons "false" [] -> (SCSeqElemsNotInSort, SCNotInSort)
            _                   -> (SCSeqElemsInSort, SCIsInSort)
  RF.VOP "ground-equals" [e1,e2] -> case p of 
    (RF.PCons "false" []) -> SCInequality (expr2term e1) (expr2term e2)
    _                     -> SCEquality (expr2term e1) (expr2term e2)
  _ -> SCPatternMatch (expr2term e) (tPattern p)
gR (LOW.Commit t)     = return [F.RewriteTarget (tTerm t)]
gR (LOW.Unobserv _)   = return []
gR (LOW.Many "~>" t x Nothing) = 
  return [F.CheckSideCondition (SCPatternMatch (tTerm t) (PMetaVar (show x)))]
gR _ = IML.warn ("disallowed action in rewrite rule") >> return []

genSteps :: LOW.Stmts -> IML.ProMan [F.FStepStmt]
genSteps ssAll = gS ssAll
  where gS :: LOW.Stmts -> IML.ProMan [F.FStepStmt]
        gS [] = return []
        gS (s:ss) = case s of 
          LOW.Branches sss -> -- assuming ss == []
                              (:[]) . F.SBranches <$> mapM genSteps sss
          LOW.PM_Args ps -> do
            r' <- fmap F.FRewriteStmt <$> gR s
            (r'++) <$> gS ss
          LOW.PM _ _ -> do 
            r' <- fmap F.FRewriteStmt <$> gR s
            (r' ++) <$> gS ss
          LOW.Commit t -> (F.StepTarget (tTerm t):) <$> gS ss
          LOW.Many "~>" _ _ Nothing -> do
            r' <- fmap F.FRewriteStmt <$> gR s
            (r'++) <$> gS ss
          LOW.Unobserv _ -> gS ss
          LOW.Single "->" t x (Just l) -> 
            let prem = F.Premise (tTerm t) (tMVar x)
            in case last ss of
              -- hard-coded pattern for else and handle-thrown
              -- because setScope is not used in this case,
              -- there is no setting of inherited entities
              LOW.Branches [(r1@(LOW.WO_Get nm1 x1 l1):rest1)
                           ,(r2@(LOW.WO_Get nm2 x2 l2):rest2)]
                | l == l1, l == l2 -> do
                  init' <- gS (init ss)
                  res1 <- gS rest1
                  res2 <- gS rest2
                  hd1  <- gS [r1]
                  hd2  <- gS [r2]
                  return (F.ReceiveControl nm2 prem : init' ++ 
                              [F.SBranches [hd1++res1,hd2++res2]])
              _ -> (foldr (setScope l) prem ssAll:) <$> gS ss
          LOW.RO_Get nm x -> (F.ReadInherited nm (tMVar x):) <$> gS ss
          LOW.RW_Get nm x _ -> (F.ReadMutable nm (tMVar x):) <$> gS ss
          LOW.WO_Get "failed-nothing" x _ -> 
            (F.ReadControl "failed" Nothing:) <$> gS ss
          LOW.WO_Get "failed" x _ ->  
            (F.ReadControl "failed" (Just $ tMVar x):) <$> gS ss
          LOW.WO_Get "thrown-nothing" x _ -> 
            (F.ReadControl "thrown" Nothing:) <$> gS ss
          LOW.WO_Get "thrown" x _ -> 
            (F.ReadControl "thrown" (Just $ tMVar x):) <$> gS ss
          LOW.WO_Get _ _ _ -> gS ss
          LOW.RO_Set _ _ _ -> gS ss
          LOW.RW_Set nm e _ -> (F.WriteMutable nm (expr2term e):) <$> gS ss
        -- TODO split into control and output, without hard-coding
          LOW.WO_Set "failed-nothing" e -> gS ss
          LOW.WO_Set "failed" e -> 
            (F.WriteControl "failed" (Just $ expr2term e) :) <$> gS ss
          LOW.WO_Set "thrown-nothing" e -> gS ss 
          LOW.WO_Set "thrown" e -> 
            (F.WriteControl "thrown" (Just $ expr2term e) :) <$> gS ss
          LOW.WO_Set nm e -> (F.WriteOutput nm (expr2term e) :) <$> gS ss
          LOW.Many _ _ _ _ -> IML.warn ("unrecognised premise") >> gS ss
          LOW.Single _  _ _ _ -> IML.warn ("unrecognised premise") >> gS ss 

        setScope :: Int -> LOW.Stmt -> F.FStepStmt -> F.FStepStmt 
        -- TODO split into control and output, without hard-coding
        setScope l s acc = case s of
          LOW.WO_Get nm x l' | l == l' -> tWO_Get nm x acc
          LOW.RO_Set nm e l' | l == l' -> F.ScopeInherited nm (expr2term e) acc
          _                            -> acc

{-        mergePatterns :: [F.StepStmt] -> [F.StepStmt]
        mergePatterns [] = []
        mergePatterns (s:ss) = case (s,ss) of
          (F.Premise t p, F.SBranches [F.ReceiveControl nm mp
          _   -> s : mergePatterns ss-}

        tWO_Get "thrown" x acc = F.ReceiveControl "thrown" acc 
        tWO_Get "thrown-nothing" x acc = F.ReceiveControl "thrown" acc
        tWO_Get "failed" x acc = F.ReceiveControl "failed" acc
        tWO_Get "failed-nothing" x acc = F.ReceiveControl "failed" acc
        tWO_Get nm x acc = F.ReceiveOutput nm (tMVar x) acc

de_explicate :: [F.FStepStmt] -> [F.FStepStmt]
de_explicate [] = []
de_explicate (F.SBranches sss:_) = [F.SBranches (map de_explicate sss)]
de_explicate [x] = [x]
de_explicate (x:y:ys) = case (x,y) of
  (F.FRewriteStmt (F.CheckSideCondition (SCPatternMatch t (PMetaVar v1)))
     ,F.Premise (TVar v1') p) | v1 == v1', not (v1 `elem` readVars ys)
         -> F.Premise t p : de_explicate ys
  (F.FRewriteStmt (F.CheckSideCondition (SCPatternMatch t (PMetaVar v1)))
     ,F.FRewriteStmt (F.CheckSideCondition (SCIsInSort (TVar v1') t2)))
       | v1 == v1', not (v1 `elem` readVars ys)  
         -> F.FRewriteStmt (F.CheckSideCondition (SCIsInSort t t2))
             : de_explicate ys
  (F.FRewriteStmt (F.CheckSideCondition (SCPatternMatch t (PMetaVar v1)))
     ,F.FRewriteStmt (F.CheckSideCondition (SCNotInSort (TVar v1') t2))) 
       | v1 == v1', not (v1 `elem` readVars ys)  
         -> F.FRewriteStmt (F.CheckSideCondition (SCNotInSort t t2)) 
             : de_explicate ys
  _ -> x : de_explicate (y:ys)

de_explicateR :: [F.FRewriteStmt] -> [F.FRewriteStmt]
de_explicateR [] = []
de_explicateR (F.RBranches sss:_) = [F.RBranches (map de_explicateR sss)]
de_explicateR [x] = [x]
de_explicateR (x:y:ys) = case (x,y) of
  (F.CheckSideCondition (SCPatternMatch t (PMetaVar v1))
     ,F.CheckSideCondition (SCIsInSort (TVar v1') t2))
       | v1 == v1', not (v1 `elem` readVars ys)  
         -> F.CheckSideCondition (SCIsInSort t t2)
             : de_explicateR ys
  (F.CheckSideCondition (SCPatternMatch t (PMetaVar v1))
     ,F.CheckSideCondition (SCNotInSort (TVar v1') t2))
       | v1 == v1', not (v1 `elem` readVars ys)  
         -> F.CheckSideCondition (SCNotInSort t t2)
             : de_explicateR ys
  _ -> x : de_explicateR (y:ys)

tPatterns :: [RF.Pattern] -> [FPattern]
tPatterns = map tPattern

-- problematic: how to translate arbitrary value-representation
-- fortunately only very few literals will be translated into
-- patterns, so we should be able to extract them (TODO)
tPattern :: RF.Pattern -> FPattern
tPattern (RF.PCons "tuple" ps)  = PTuple (map tPattern ps)
tPattern (RF.PCons "list" ps)   = PList (map tPattern ps)
tPattern (RF.PAny)              = PAny
tPattern (RF.PCons "natural-literal" [RF.PCons n []]) = PLit (FLiteralNat (read n))
tPattern (RF.PCons "float-literal" [RF.PCons f []]) = PLit (FLiteralFloat (read f))
tPattern (RF.PCons "string-literal" [RF.PCons s []]) = PLit (FLiteralString s)
tPattern (RF.PCons "atom-literal" [RF.PCons a []]) = PLit (FLiteralAtom (read a))
tPattern (RF.PCons "__annotated-pattern" 
            [pat, RF.PCons "__embedded-valsorts" [RF.PCons sort []]]) = 
  PAnnotated (tPattern pat) (read sort) 
tPattern (RF.PVar v) = tMVar v 
tPattern (RF.PCons cs ps) = PADT cs (map tPattern ps)

tMVar :: RF.MVar -> FPattern
tMVar (RF.MVar x 1 (Just 1))  = PMetaVar x
tMVar (RF.MVar x 0 Nothing)   = PSeqMetaVar x StarOp
tMVar (RF.MVar x 1 Nothing)   = PSeqMetaVar x PlusOp 
tMVar (RF.MVar x 0 (Just 1))  = PSeqMetaVar x QuestionMarkOp
tMVar v                       = error ("unknown kind of meta-variable" ++ show v)

tTerm :: RF.Term -> FTerm
tTerm (RF.TVar (RF.MVar var _ _)) = TVar var
tTerm (RF.TCons False "__tuple" ts) = TTuple (map tTerm ts)
tTerm (RF.TCons False "__list" ts) = TList (map tTerm ts)
tTerm (RF.TCons False "__set" ts) = TSet (map tTerm ts) 
tTerm (RF.TCons False "__map" ts) = TMap (map tTerm ts)
tTerm (RF.TCons False "TSortUnion" [t1,t2]) = TSortUnion (tTerm t1) (tTerm t2)
tTerm (RF.TCons False "TSortComputes" [t1]) = TSortComputes (tTerm t1) 
tTerm (RF.TCons False "TSortComputesFrom" [t1,t2]) = 
  TSortComputesFrom (tTerm t1) (tTerm t2)
tTerm (RF.TCons False "TSortSeq" [t, RF.TCons False op []]) = 
  TSortSeq (tTerm t) (read op) 
tTerm (RF.TCons True "__some-funcon-value" [RF.TCons True fv []]) = 
  TFuncon (FValue (read fv)) 
tTerm (RF.TCons False "__some-funcon" [RF.TCons False f []]) = TFuncon (read f) 
tTerm (RF.TCons False cs []) = TName (pack cs) 
tTerm (RF.TCons False cs [t]) = TApp (pack cs) (tTerm t)
tTerm (RF.TCons True _ _) = error "missing value translation"

expr2term :: RF.Expr -> FTerm
expr2term (RF.Val t) = tTerm t
expr2term (RF.VOP op es) = TApp (pack op) (TTuple $ map expr2term es)

printStmts :: [LOW.Stmts] -> String
printStmts = unlines . intersperse "\n" . map (render . ppStmts)
