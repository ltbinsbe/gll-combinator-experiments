{-# LANGUAGE OverloadedStrings #-}

module Simplify.LiftStrictness where

import Types.SourceAbstractSyntax (SeqSortOp(..))
import Types.CoreAbstractSyntax (FSig(..), FTerm(..), FPattern (..)
                                ,Strictness(..))
import Types.TargetAbstractSyntax hiding (FPattern(..))

import Data.Text (pack)
import CCO.Component

lift_strictness :: Component CBSFile CBSFile
lift_strictness = component (return . lCBSFile)

lCBSFile :: CBSFile -> CBSFile
lCBSFile cbsf = doToFuncons lFSpec cbsf

lFSpec :: FunconSpec -> FunconSpec
lFSpec spec@(FRules nm sig mcs rs ss) = case sig of  
  FLazy               -> spec
  FNullary            -> spec
  FStrict             -> FRules nm FLazy mcs rs ss'
    where ss' = rule : ss
          rule = FStepRule step [Left premise]
          step = FStep  [PAnnotated (PSeqVar "V*" StarOp) 
                          (TSortSeq (TName "values") StarOp)
                        ,PMetaVar "X"
                        ,PSeqVar "Y*" StarOp]
                        (TApp (pack nm) [TVar "V*", TVar "X'", TVar "Y*"])
                        [] [] [] [] []
          premise = FPremiseStep (TVar "X") (PMetaVar "X'") [] [] [] [] []
  FPartiallyLazy _ (Just _) -> FRules nm FLazy mcs rs ss'
    where ss' = rule : ss
          rule = FStepRule step [Left premise]
          step = FStep  [PAnnotated (PSeqVar "V*" StarOp) 
                          (TSortSeq (TName "values") StarOp)
                        ,PMetaVar "X"
                        ,PSeqVar "Y*" StarOp]
                        (TApp (pack nm) [TVar "V*", TVar "X'", TVar "Y*"])
                        [] [] [] [] []
          premise = FPremiseStep (TVar "X") (PMetaVar "X'") [] [] [] [] []
  FPartiallyLazy ann Nothing -> FRules nm FLazy mcs rs ss'
    where ss'       = map mkRule ruleKeys ++ ss
          ruleKeys  = map fst $ filter ((Strict ==) . snd) keys
          keys      = zip [1..] ann

          mkRule k  = FStepRule step [Left premise] 
            where step = FStep pats (TApp (pack nm) terms) [] [] [] [] [] 
                  (pats,terms) = foldr op ([],[]) keys
                    where op (k',sness) (pats, terms) 
                            | k' == k = (PMetaVar var:pats
                                        ,TVar (var ++ "'") : terms) 
                            | k' <  k, Strict <- sness = 
                                (PAnnotated (PMetaVar var) 
                                    (TName "values"):pats
                                ,TVar var : terms)
                            | True    = (PMetaVar var : pats, TVar var : terms)
                           where var = "X" ++ show k'
                  premise = FPremiseStep (TVar var) (PMetaVar (var ++ "'")) 
                              [] [] [] [] []
                    where var = "X" ++ show k 
