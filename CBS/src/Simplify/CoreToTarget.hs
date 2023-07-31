{-# Language FlexibleContexts, ScopedTypeVariables, LambdaCase, MultiParamTypeClasses, TupleSections, FlexibleInstances, OverloadedStrings #-}

-- | 
-- Sanity checking and simplifications regarding:
--
--  * input entities
module Simplify.CoreToTarget where

import CCO.Component (Component, component)
import CCO.Feedback (Feedback, errorMessage)
import CCO.Printing (wrapped)

import Control.Applicative
import Control.Arrow ((***))
import Control.Monad.Except

import Simplify.Utils

import Data.Either (lefts)
import Data.Maybe (catMaybes)
import Data.Text (pack)


--------------------------------------------------------------------

import Funcons.EDSL (FTerm(TVar), string_, HasTypeVar(..), limitedSubsTypeVarWildcard, showOp, SeqSortOp(..))

import Types.SourceAbstractSyntax (Name, MetaVar)
import Types.Bindings(HasPatVar(..))
import Types.CoreAbstractSyntax

import qualified Types.TargetAbstractSyntax as T

--------------------------------------------------------------------

-- require for forming a pipeline with uu-cco library
core2target :: Component CBSFile T.CBSFile
core2target = component simplifyCBSFile

instance MonadError String Feedback where
    throwError = errorMessage . wrapped

--------------------------------------------------------------------

simplifyCBSFile :: MonadError String m => CBSFile -> m T.CBSFile
simplifyCBSFile (CBSFile file env als) = 
  T.CBSFile <$> (concat <$> mapM (simplifySpecs env) file) 
            <*> return env <*> return als

simplifySpecs :: MonadError String m => TypeEnv -> CBSSpec -> m [T.CBSSpec]
simplifySpecs env (FunconSpec fspec) = return . T.FunconSpec <$> simplifyFSpec env fspec
simplifySpecs env (DataTypeSpec spec) = return [T.DataTypeSpec spec]
simplifySpecs env (EntitySpec spec) = return [T.EntitySpec spec]
simplifySpecs env (MetaSpec spec) = return [T.MetaSpec spec]
simplifySpecs env (ConsSpec spec) =  
  return (T.FunconSpec (simplifyConsSpec spec) : [T.ConsSpec spec])

--------------------------------------------------------------------

simplifyConsSpec :: ConsSpec -> T.FunconSpec
simplifyConsSpec (ValCons nm (TypeCons ss) pattypes _ _) = 
  genValConsFuncons nm ss "non-strict-datatype-value" pattypes
simplifyConsSpec (ValCons nm sig pattypes _ _) = 
  genValConsFuncons nm sig "datatype-value" pattypes
  where sig = if null pattypes then FNullary else FStrict

genValConsFuncons nm sig cons pattypes =   
  T.FRules nm sig Nothing [rule] []
  where rule  = T.FRewriteRule pats (Just (TApp cons (cname:args))) scds
        cname = TFuncon (string_ nm)  
        args  = map (TVar . fst) vars
        pats  = zipWith mkPat vars pattypes
                -- sorts are ignored (no substitution available)
          where mkPat (var, mop) sort = msvar 
                  where msvar = case mop of Nothing -> PMetaVar var
                                            Just op -> PSeqVar var op
--        sides = zipWith mkSide vars pattypes
--          where mkSide (var,mop) sort = SCIsInSort (TVar var) sort 
        vars  = zipWith mkOp [1..] pattypes
          where mkOp i pat = case pat of 
                  TSortSeq _ op -> var $ Just op
                  TSortPower _ _ -> var $ Just StarOp
                  TVar str      -> case last str of
                            '*' -> var $ Just StarOp
                            '?' -> var $ Just QuestionMarkOp
                            '+' -> var $ Just PlusOp
                            _   -> var Nothing
                  _             -> var Nothing
                  where var mop = ("_X" ++ show i ++ maybe "" showOp mop, mop)
        scds  = case sig of FStrict -> map (uncurry toVal) vars
                              where toVal x mop = case mop of
                                      Just op -> SCIsInSort (TVar x) (TSortSeq (TName "values") op) 
                                      Nothing -> SCIsInSort (TVar x) (TName "values")
                            _       -> []

simplifyFSpec :: MonadError String m => TypeEnv -> FunconSpec -> m T.FunconSpec
simplifyFSpec env (FRules nm sig mdoc rews steps) =
   T.FRules nm sig mdoc <$> mapM (simplifyRewrite env) rews 
                        <*> mapM (simplifyFStepRule env) steps

simplifyRewrite :: MonadError String m => TypeEnv -> FRewriteRule -> m T.FRewriteRule
simplifyRewrite env rule@(FRewriteRule pats rhs conds) = -- TODO why do we need a different FRewriteRule datatype?
   return (limitedSubsTypeVarWildcard (pvars rule) (Just (TName "values")) env $ T.FRewriteRule pats rhs conds)

simplifyFStepRule :: MonadError String m => TypeEnv -> FStepRule -> m T.FStepRule
simplifyFStepRule env rule@(FStepRule step pcs) =
   do b <- checkInputRouting step (lefts pcs)
      guardM b "Unsupported routing between input entities."
      limitedSubsTypeVarWildcard (pvars rule) (Just (TName "values")) env <$> 
        (T.FStepRule <$> simplifyFStep step <*> mapM (traverseEither simplifyFPremiseStep return) pcs)

--------------------------------------------------------------------

{-
simplifyF2TPattern :: MonadError String m => FPattern -> m T.TPattern
simplifyF2TPattern p = case p of
  PTuple ps   -> T.TPADT "tuples" <$> mapM simplifyF2TPattern ps 
  PList [p]   -> T.TPADT "lists" . (:[]) <$> simplifyF2TPattern p
  PList ps    -> throwError "cannot simplify list-notation to type-pattern"
  PAnnotated pat s -> simplifyF2TPattern pat
  PADT cons ps  -> T.TPADT (pack cons) <$> mapM simplifyF2TPattern ps
  PAny        -> return $ T.TPWildCard
  PLit lit    -> return $ T.TPLit (TFuncon $ simplifyLiteral lit)
  PMetaVar var -> return $ T.TPVar var 
  PSeqMetaVar var op -> return $ T.TPSeqVar var op
-}

simplifyFStep :: MonadError String m => FStep -> m T.FStep
simplifyFStep st =
       return $ T.FStep
                 { T.stepSource = stepSource st
                 , T.stepTarget = stepTarget st
                 , T.stepInheritedEntities = stepInheritedEntities st
                 , T.stepMutableEntities = stepMutableEntities st
                 , T.stepInputEntities = map (\(n,ps,_) -> (n,ps)) 
                                          (stepInputEntities st)
                 , T.stepOutputEntities = stepOutputEntities st
                 , T.stepControlEntities = stepControlEntities st
                 }

simplifyInputEntity :: MonadError String m => (Name,[FPattern],[MetaVar]) -> m (Name,[MetaVar])
simplifyInputEntity (n,ps,_) = (n,) <$> mapM patToMV ps
  where
    patToMV (PMetaVar mv) = return mv
    patToMV _             = throwError "Currently we only allow meta-variables in input patterns."  -- TODO: could also allow underscores

simplifyFPremiseStep :: MonadError String m => FPremiseStep -> m T.FPremiseStep
simplifyFPremiseStep pst =
       return $ T.FPremiseStep
                 { T.premiseSource = premiseSource pst
                 , T.premiseTarget = premiseTarget pst
                 , T.premiseInheritedEntities = premiseInheritedEntities pst
                 , T.premiseMutableEntities = premiseMutableEntities pst
                 , T.premiseInputEntities = map simplifyInputEntityPremise (premiseInputEntities pst)
                 , T.premiseOutputEntities = premiseOutputEntities pst
                 , T.premiseControlEntities = premiseControlEntities pst
                 }

simplifyInputEntityPremise :: (Name,[FTerm],Maybe MetaVar) -> (Name,[FTerm],T.InputAccess)
simplifyInputEntityPremise (n,ts,Nothing) = (n,ts,T.ExactInput)
simplifyInputEntityPremise (n,ts,Just _)  = (n,ts,T.ExtraInput)

--------------------------------------------------------------------

checkInputRouting :: forall m. MonadError String m => FStep -> [FPremiseStep] -> m Bool
checkInputRouting step psteps =
  and <$> mapM (\(n,_,mvs) -> (mvs ==) <$> catMaybes <$> mapM (premiseMv n) psteps) (stepInputEntities step)
    where
      premiseMv :: Name -> FPremiseStep -> m (Maybe MetaVar)
      premiseMv n pstep = case lookup2 n (premiseInputEntities pstep) of
                            Nothing      -> throwError "Mismatched input entity in rule" -- do we check this earlier?
                            Just (_,mmv) -> return mmv

--------------------------------------------------------------------
