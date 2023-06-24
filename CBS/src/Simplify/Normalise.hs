-- TODO 
--  * check for duplicate variables
--  * check whether all readVars are defined 
--      (given dependency based sorting, we dont have to check order)
--  * check for duplicate readVars and generate EnvRewrite for them
--  * remove duplicate EnvRewrite 

module Simplify.Normalise where

import Types.CoreAbstractSyntax (FSideCondition(..), FValSorts(..), FTerm(..),FPattern(..))
import Types.FunconModule 
import Types.Sequentialisation (AccessesEnv(..))
import Types.SourceAbstractSyntax (MetaVar)

import Data.List(intersect,sortBy)
import Control.Applicative
import Control.Monad.State

import CCO.Component

normalise :: Component FunconModule FunconModule
normalise = component (return . nFModule)

nFModule :: FunconModule -> FunconModule
nFModule fmod = fmod {funcons = nFSpecs (funcons fmod)}

nFSpecs :: [FunconSpec] -> [FunconSpec]
nFSpecs = map nFSpec 

nFSpec :: FunconSpec -> FunconSpec
nFSpec (FunconSpec nm sig mdoc rss sss) = 
  FunconSpec nm sig mdoc (nRStmts rss) (nSStmts sss)

nSStmts :: [[FStepStmt]] -> [[FStepStmt]]
nSStmts = {- nSStmtsSort {- broken after removal of PremiseBlock?-} .-} 
            nSStmtsExplRew . nSStmtsRemAnn

nRStmts :: [[FRewriteStmt]] -> [[FRewriteStmt]]
nRStmts = nRStmtsSort . nRStmtsRemAnn

nSStmtsSort :: [[FStepStmt]] -> [[FStepStmt]]
nSStmtsSort = map nSStmtSort 

-- should be inefficient, as readVars and writeVars of a statement are being recomputed 
-- however, the statements (and terms they embed) will be small
nSStmtSort :: [FStepStmt] -> [FStepStmt]
nSStmtSort = sortBy varDepOrder

nRStmtsSort :: [[FRewriteStmt]] -> [[FRewriteStmt]]
nRStmtsSort = map nRStmtSort 

nRStmtSort :: [FRewriteStmt] -> [FRewriteStmt]
nRStmtSort = sortBy varDepOrder

nSStmtsRemAnn :: [[FStepStmt]] -> [[FStepStmt]]
nSStmtsRemAnn = map nSStmtRemAnn

nRStmtsRemAnn :: [[FRewriteStmt]] -> [[FRewriteStmt]]
nRStmtsRemAnn = map nRStmtRemAnn

nSStmtRemAnn :: [FStepStmt] -> [FStepStmt]
nSStmtRemAnn = concatMap op
  where op (FRewriteStmt r) = map FRewriteStmt (nRStmtRemAnn [r])
        op s                = [s] 

nRStmtRemAnn :: [FRewriteStmt] -> [FRewriteStmt]
nRStmtRemAnn [] = []
nRStmtRemAnn (pmatch:rest) = case pmatch of 
  ArgsPattern pvar pats -> 
    let (pats', sortchecks) = removeAnnotations pats
    in (ArgsPattern pvar pats'):sortchecks++rest
  _ -> pmatch:rest
 where
  removeAnnotations = foldr op ([], [])
    where op pat (pats', checks) = case pat of
            -- TODO what about sequence variables?
            PAnnotated pat@(PMetaVar var) (FSingletonValSort ty) -> 
                  (pat:pats', CheckSideCondition (SCIsInSort (TVar var) ty):checks)
            pat -> (pat:pats', checks)

type VarGen a = State Int a 

getNewVar :: VarGen MetaVar 
getNewVar = modify (+1) >> get >>= (\i -> return ("_" ++ show i))

-- explicate rewrites
nSStmtsExplRew :: [[FStepStmt]] -> [[FStepStmt]]
nSStmtsExplRew [] = []
-- variables are generated per rule
nSStmtsExplRew (rule:rules) = rule' : nSStmtsExplRew rules
  where rule' = evalState (nSStmtExpRew rule) 0 

nSStmtExpRew :: [FStepStmt] -> VarGen [FStepStmt]
nSStmtExpRew ss = do  
  exps <- mapM explicate ss
  return $ concat $ [ (rewrites++[ss']) | (rewrites, ss') <- exps]
  where explicate :: FStepStmt -> VarGen ([FStepStmt], FStepStmt)
        -- TODO explicate other abstract statements
        explicate (Premise term pat) = case term of 
          TVar mv -> return ([FRewriteStmt $ EnvRewrite mv], Premise term pat)
          _       -> do   
            mv <- getNewVar 
            return ([FRewriteStmt $ EnvStore mv term, FRewriteStmt $ EnvRewrite mv]
                   ,Premise (TVar mv) pat)
        explicate (PremiseBlock s) = mapSnd PremiseBlock <$> explicate s
        explicate (ReceiveControl nm s) = mapSnd (ReceiveControl nm) <$> explicate s
        explicate (ReceiveOutput nm p s)  = mapSnd (ReceiveOutput nm p) <$> explicate s
        explicate (ScopeInput nm vs e s)  = mapSnd (ScopeInput nm vs e) <$> explicate s
        explicate (ScopeInherited nm t s) = mapSnd (ScopeInherited nm t) <$> explicate s
        explicate s = return ([], s)
  
mapSnd f (a,b) = (a,f b)

-- | Defines an ordering between abstract statements.
-- Assumes:
--  * varDepOrder is only applied to two statements 
--      contained in the sequentialisation of the same rule
--  * no two pattern in the same rule contain the same variable
varDepOrder :: (Ord a, AccessesEnv a) => a -> a -> Ordering
varDepOrder x y | intersect (writeVars x) (readVars y) /= [] = LT
                | intersect (writeVars y) (readVars x) /= [] = GT
                | otherwise                                  = x `compare` y
