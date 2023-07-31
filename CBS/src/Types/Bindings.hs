module Types.Bindings where

import Types.SourceAbstractSyntax (MetaVar)

import qualified Types.CoreAbstractSyntax as C

import qualified Data.Set as S

class HasPatVar a where
  pvars :: a -> S.Set MetaVar

instance HasPatVar a => HasPatVar [a] where
  pvars c = S.unions $ fmap pvars c

instance (HasPatVar a, HasPatVar b) => HasPatVar (Either a b) where
  pvars (Left l) = pvars l
  pvars (Right r) = pvars r

instance (HasPatVar a) => HasPatVar (Maybe a) where
  pvars (Just j)  = pvars j
  pvars Nothing   = S.empty

instance HasPatVar C.FRewriteRule where
  pvars (C.FRewriteRule ps _ ss) = pvars ps `S.union` pvars ss

instance HasPatVar C.FPattern where
  pvars p = case p of 
    C.PMetaVar v -> S.singleton v
    C.PSeqVar v _ -> S.singleton v
    C.PAnnotated pat _ -> pvars pat
    C.PWildCard -> S.empty 
    C.PValue vpat -> pvars vpat

instance HasPatVar C.VPattern where
  pvars p = case p of 
    C.PADT _ ps -> S.unions $ fmap pvars ps
    C.VPWildCard -> S.empty
--    C.PList ps -> S.unions $ fmap pvars ps
    C.VPMetaVar var -> S.singleton var
    C.VPSeqVar var _ -> S.singleton var
    C.VPLit _ -> S.empty
    C.VPAnnotated pat _ -> pvars pat
    C.VPType tpat -> pvars tpat

instance HasPatVar C.TPattern where
  pvars p = case p of
    C.TPWildCard -> S.empty
    C.TPVar var -> S.singleton var
    C.TPSeqVar var _ -> S.singleton var
    C.TPLit _ -> S.empty
    C.TPComputes pat -> pvars pat
    C.TPComputesFrom f t -> pvars f `S.union` pvars t
    C.TPADT _ ps -> S.unions $ fmap pvars ps

instance HasPatVar C.FSideCondition where
  pvars sc = case sc of 
    C.SCPatternMatch _ p -> pvars p
    _ -> S.empty

instance HasPatVar C.FStepRule where
  pvars (C.FStepRule step scs) = pvars step `S.union` pvars scs

instance HasPatVar C.FStep where
  pvars step =  pvars (C.stepSource step) 
      `S.union` pvars (map snd $ C.stepInheritedEntities step)
      `S.union` pvars (map (\(_,x,_) -> x) $ C.stepMutableEntities step)
      `S.union` pvars (concatMap (\(_,x,_) -> x) $ C.stepInputEntities step)
      `S.union` S.fromList (concatMap (\(_,_,x) -> x) $ C.stepInputEntities step)
      `S.union` pvars (map snd $ C.stepControlEntities step)

instance HasPatVar C.FPremiseStep where
  pvars premise =  pvars (C.premiseTarget premise) 
      `S.union` pvars (map (\(_,_,x) -> x) $ C.premiseMutableEntities premise)
      `S.union` S.fromList (concatMap (\(_,_,x) -> maybe [] (:[]) x) $ C.premiseInputEntities premise)
      `S.union` pvars (map snd $ C.premiseOutputEntities premise)
      `S.union` pvars (map snd $ C.premiseControlEntities premise)

  
