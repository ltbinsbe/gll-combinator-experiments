-- This is a version of CoreAbstractSyntax
--  with some modifications helpful towards code-generation.
-- Information not needed for code generation has been discarded.
module Types.TargetAbstractSyntax 
  (module Types.TargetAbstractSyntax
  ,TPattern(..), FCT.FPattern(..), VPattern(..)) where

import Types.ConcreteSyntax (MetaSpec)
import Types.SourceAbstractSyntax hiding (CBSFile(..),CBSSpec(..),EntitySpec,FunconSpec,FSig,FStep(..),FPremiseStep(..),FSideCondition(..),DataTypeAlt(..), DataTypeSpec(..),FTerm(..),FPattern(..), CommentPart(..),cbs, FValSort, TypeEnv)
import Types.CoreAbstractSyntax hiding (CBSSpec(..),FunconSpec(..),FStepRule(..),FRewriteRule(..),FStep(..),FPremiseStep(..),CBSFile(..),cbs)
import Funcons.EDSL (TypeEnv, HasTypeVar(..), TPattern(..),  VPattern(..))
import qualified Funcons.EDSL as FCT

data CBSFile = CBSFile {cbs :: [CBSSpec], env :: TypeEnv, aliases :: AliasMap}

data CBSSpec = FunconSpec FunconSpec
             | DataTypeSpec DataTypeSpec
             | EntitySpec EntitySpec
             | MetaSpec MetaSpec
             | ConsSpec ConsSpec 
               deriving (Show)

funcons       :: CBSFile -> [FunconSpec]
entities      :: CBSFile -> [EntitySpec]
datatypes     :: CBSFile -> [DataTypeSpec]
metadata      :: CBSFile -> [MetaSpec]
constructors  :: CBSFile -> [ConsSpec]

funcons = foldr op [] . cbs
  where op (FunconSpec f) xs = (f:xs)
        op _ xs = xs
entities = foldr op [] . cbs
  where op (EntitySpec e) xs = e:xs
        op _ xs = xs
datatypes = foldr op [] . cbs
  where op (DataTypeSpec d) xs = d:xs
        op _ xs = xs
metadata = foldr op [] . cbs
  where op (MetaSpec f) xs = f:xs 
        op _ xs = xs
constructors = foldr op [] . cbs
  where op (ConsSpec f) xs = f:xs 
        op _ xs = xs

doToFuncons :: (FunconSpec -> FunconSpec) -> CBSFile -> CBSFile
doToFuncons f file = file{cbs = map op $ cbs file}
  where op (FunconSpec spec) = FunconSpec (f spec)
        op spec              = spec

-- TODO migrate commentpart to meta-data?
data FunconSpec = FRules Name FSig (Maybe [CommentPart]) [FRewriteRule] [FStepRule]
                  deriving (Show)

data FStepRule = FStepRule FStep [Either FPremiseStep FSideCondition]
                 deriving (Show)

data FRewriteRule = FRewriteRule [FPattern] (Maybe FTerm) [FSideCondition]
                    deriving (Show)

data FStep = FStep
               { stepSource :: [FPattern]
               , stepTarget :: FTerm
               , stepInheritedEntities :: [(Name,FPattern)]
               , stepMutableEntities :: [(Name,FPattern,FTerm)]
               , stepInputEntities :: [(Name,[FPattern])]
               , stepOutputEntities :: [(Name,FTerm)]
               , stepControlEntities :: [(Name,Maybe FPattern)]
               }
               deriving (Eq,Ord,Show)

data FPremiseStep = FPremiseStep
                      { premiseSource :: FTerm
                      , premiseTarget :: FPattern
                      , premiseInheritedEntities :: [(Name,FTerm)]
                      , premiseMutableEntities :: [(Name,FTerm,FPattern)]
                      , premiseInputEntities :: [(Name,[FTerm],InputAccess)]
                      , premiseOutputEntities :: [(Name,FPattern)]
                      , premiseControlEntities :: [(Name,Maybe FPattern)]
                      }
                      deriving (Eq,Ord,Show)

data InputAccess = ExactInput | ExtraInput
                   deriving (Eq,Ord,Show)

instance HasTypeVar FSideCondition where
  subsTypeVarWildcard mt env sc = case sc of 
    SCIsInSort t ty       -> SCIsInSort t (subsTypeVarWildcard mt env ty)
    SCNotInSort t ty      -> SCNotInSort t (subsTypeVarWildcard mt env ty)
    SCPatternMatch t pat  -> SCPatternMatch t (subsTypeVarWildcard mt env pat)
    SCEquality t1 t2      -> SCEquality t1 t2
    SCInequality t1 t2    -> SCInequality t1 t2
    
instance (HasTypeVar a, HasTypeVar b) => HasTypeVar (Either a b) where 
  subsTypeVarWildcard mt env (Left l) = Left $ subsTypeVarWildcard mt env l
  subsTypeVarWildcard mt env (Right r) = Right $ subsTypeVarWildcard mt env r

instance (HasTypeVar a) => HasTypeVar (Maybe a) where
  subsTypeVarWildcard mt env = fmap (subsTypeVarWildcard mt env)
instance (HasTypeVar a) => HasTypeVar [a] where
  subsTypeVarWildcard mt env = fmap (subsTypeVarWildcard mt env)

instance HasTypeVar FStepRule where
  subsTypeVarWildcard mt env (FStepRule step scs) = FStepRule (subsTypeVarWildcard mt env step) (subsTypeVarWildcard mt env scs)

instance HasTypeVar FRewriteRule where
  subsTypeVarWildcard mt env (FRewriteRule pats t scs) = FRewriteRule (subsTypeVarWildcard mt env pats) (subsTypeVarWildcard mt env t) (subsTypeVarWildcard mt env scs)

instance HasTypeVar FStep where
  subsTypeVarWildcard mt env step = step {stepSource = subsTypeVarWildcard mt env (stepSource step)
                              ,stepInheritedEntities = map (subs2of2 env) (stepInheritedEntities step)
                              ,stepMutableEntities = map (subs2of3 env) (stepMutableEntities step)
                              ,stepInputEntities = map (subs2of2 env) (stepInputEntities step)
                              ,stepControlEntities = map (subs2of2 env) (stepControlEntities step)}

instance HasTypeVar FPremiseStep where
  subsTypeVarWildcard mt env step = step {premiseTarget = subsTypeVarWildcard mt env (premiseTarget step)
                              ,premiseMutableEntities = map (subs3of3 env) (premiseMutableEntities step)
                              ,premiseOutputEntities = map (subs2of2 env) (premiseOutputEntities step)
                              ,premiseControlEntities = map (subs2of2 env) (premiseControlEntities step)}

subs2of2 :: HasTypeVar b => TypeEnv -> (a, b) -> (a, b)
subs2of2 env (a,b) = (a, subsTypeVar env b)

subs2of3 :: HasTypeVar b => TypeEnv -> (a,b,c) -> (a,b,c)
subs2of3 env (a,b,c) = (a, subsTypeVar env b,c)

subs3of3 :: HasTypeVar c => TypeEnv -> (a,b,c) -> (a,b,c)
subs3of3 env (a,b,c) = (a, b, subsTypeVar env c)

