{-# LANGUAGE LambdaCase, OverloadedStrings #-}

-- This is a simplified version of SourceAbstractSyntax.
-- Information not needed for code generation has been discarded.
module Types.CoreAbstractSyntax (
    -- copies of source
    CBSFile(..), CBSSpec(..), EntitySpec(..),FunconSpec(..),FSig(..),FStep(..),
        FPremiseStep(..), FSideCondition(..), DataTypeSpec(..), DataTypeAlt(..),
        FSort,
        -- defined here
        FStepRule(..), Strictness(..), FRewriteRule(..),
        isStrict, funconIsStrict, funconIsNullary, CommentPart(..), 
        ConsSpec(..),CSig(..),
        -- defined in the interpreter
        FTerm(..),TypeEnv, FPattern(..), VPattern(..), TPattern(..),TyAssoc(..),
    )where

import Funcons.EDSL (FTerm(..), FPattern(..), VPattern(..), TPattern(..), TypeEnv(..), TyAssoc(..), HasTypeVar(..))

import Types.ConcreteSyntax (MetaSpec(..), Term, Premise)
import Types.SourceAbstractSyntax hiding (CBSFile,CBSSpec,EntitySpec,FunconSpec,FSig(..),FStep,FPremiseStep,FSideCondition,DataTypeSpec(..), FTerm(..), FPattern(..),FSort(..),TypeEnv, TyAssoc(..), DataTypeAlt(..),FPattern(..), CommentPart(..))

data CBSFile = CBSFile {cbs :: [CBSSpec], env :: TypeEnv, aliases :: AliasMap}

data CBSSpec = FunconSpec FunconSpec
             | DataTypeSpec DataTypeSpec
             | EntitySpec EntitySpec
             | MetaSpec MetaSpec
             | ConsSpec ConsSpec
               deriving (Show)

data EntitySpec = InheritedSpec Name FTerm
                | MutableSpec Name FTerm
                | InputSpec Name
                | OutputSpec Name
                | ControlSpec Name
                  deriving (Show)

data FunconSpec = FRules Name FSig (Maybe [CommentPart]) [FRewriteRule] [FStepRule]
                  deriving (Show)

data ConsSpec = ValCons Name -- constructor name 
                        CSig -- datatype or type constructor?
                        [FSort] -- the types the arguments should have 
                        Name -- name of type for which it constructs values
                        [TPattern] -- type params for type (required for GADTs)
                deriving (Show)

data CommentPart  = Ordinary String
                  | Asterisk
                  | At String
                  | CommentTerm [Term]
                  | CommentPremise Premise
                  | SpecInComment CBSSpec
                  deriving Show

data FSig = FStrict -- fully strict, possibly variadic
          | FLazy   -- fully non-strict, possibly variadic
          | FPartiallyLazy [Strictness] -- mixed strict, non-variadic
              (Maybe Strictness) -- zero or more args with this strictness
          | FNullary -- no arguments
            deriving (Eq,Ord,Show)

data CSig = DataTypeCons
          | TypeCons FSig 
          deriving (Show)

funconIsStrict :: FSig -> Bool
funconIsStrict = \case  FStrict -> True
                        _       -> False

funconIsNullary :: FSig -> Bool
funconIsNullary = \case FNullary    -> True
                        _           -> False

data Strictness = Strict | Lazy
                  deriving (Eq,Ord,Show)

isStrict Strict = True
isStrict Lazy   = False

data FRewriteRule = FRewriteRule [FPattern] (Maybe FTerm) [FSideCondition]
                    deriving (Eq,Ord,Show)

data FStepRule = FStepRule FStep [Either FPremiseStep FSideCondition]
                 deriving (Eq,Ord,Show)

data FStep = FStep
               { stepSource :: [FPattern]
               , stepTarget :: FTerm
               , stepInheritedEntities :: [(Name,FPattern)]
               , stepMutableEntities :: [(Name,FPattern,FTerm)]
               , stepInputEntities :: [(Name,[FPattern],[MetaVar])]
               , stepOutputEntities :: [(Name,FTerm)]
               , stepControlEntities :: [(Name,Maybe FPattern)]
               }
               deriving (Eq,Ord,Show)

data FPremiseStep = FPremiseStep
                      { premiseSource :: FTerm
                      , premiseTarget :: FPattern
                      , premiseInheritedEntities :: [(Name,FTerm)]
                      , premiseMutableEntities :: [(Name,FTerm,FPattern)]
                      , premiseInputEntities :: [(Name,[FTerm],Maybe MetaVar)]
                      , premiseOutputEntities :: [(Name,FPattern)]
                      , premiseControlEntities :: [(Name,Maybe FPattern)]
                      }
                      deriving (Eq,Ord,Show)

data FSideCondition = SCEquality FTerm FTerm
                    | SCInequality FTerm FTerm
                    | SCPatternMatch FTerm FPattern
                    | SCIsInSort FTerm FSort
                    | SCNotInSort FTerm FSort
                      deriving (Eq,Ord,Show)

type FSort = FTerm

termComputes :: FSort -> Bool
termComputes (TSortComputes _) = True
termComputes (TSortComputesFrom _ _) = True
termComputes _  = False

data DataTypeSpec = DataTypeDecl Name [TPattern] [DataTypeAlt]
                    deriving (Show)

data DataTypeAlt = DataTypeInclusion FSort
                   deriving (Eq,Ord,Show)

{-
data FPattern = PTuple [FPattern]
              | PList [FPattern]
              | PAnnotated FPattern FSort
              | PADT ADTConstructor [FPattern]
              | PAny
              | PLit FLiteral
              | PMetaVar MetaVar
              | PSeqMetaVar MetaVar SeqSortOp  -- Note: the MetaVar should also contain the operator suffix
                deriving (Eq,Ord,Show)
-}
-------------------------------------------------

{-
instance HasTypeVar FPattern where
  subsTypeVarWildcard mt env pat = case pat of
    PAnnotated p   t    -> PAnnotated (subsTypeVarWildcard mt env p) (subsTypeVarWildcard mt env t)
    PADT n pats         -> PADT n (map (subsTypeVarWildcard mt env) pats)
    PTuple pats         -> PTuple (map (subsTypeVarWildcard mt env) pats)
    PList pats          -> PList (map (subsTypeVarWildcard mt env) pats)
    PMetaVar var        -> PMetaVar var
    PSeqMetaVar var op  -> PSeqMetaVar var op
    PLit v              -> PLit v
    PAny                -> PAny
-}
