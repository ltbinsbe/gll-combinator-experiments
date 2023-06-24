module Types.SourceAbstractSyntax (
    -- defined here
    CBSFile(..), CBSSpec(..), TypeSynonymSpec(..), DataTypeSpec(..),
    EntitySpec(..), FunconSpec(..), FRule(..), FSideCondition(..),
    FSig(..), FParam(..), ParamPattern(..), Name, FStep(..), FPremiseStep(..),
    FPattern(..), FLiteral(..), ADTConstructor, 
    FSort, TypeEnv, TyAssoc(..), AliasMap, my_aliases,
    MetaVar, FTerm(..), DataTypeAlt(..),
    CommentPart(..), isStrictParam, isStrictSort, termArgs, isVariadic,
    -- defined in Funcons.EDSL
    SeqSortOp(..),
    ) where

import Funcons.EDSL (SeqSortOp(..))
import Types.ConcreteSyntax (MetaSpec(..), Term, Premise)

import qualified Data.Map as M

type Name = String

data CBSFile = CBSFile {cbs :: [CBSSpec], env :: TypeEnv, aliases :: AliasMap }

type TypeEnv = M.Map MetaVar TyAssoc
data TyAssoc = ElemOf FSort | SubTyOf FSort  
type AliasMap = M.Map Name [Name]

my_aliases :: Name -> AliasMap -> [Name]
my_aliases nm als = my_aliases' [] nm als
  where my_aliases' ctx nm als 
          | nm `elem` ctx = error "cyclic aliases"
          | otherwise = nm : concatMap (\n -> my_aliases' (nm:ctx) n als) 
                          (maybe [] id (M.lookup nm als))

data CBSSpec = FunconSpec FunconSpec
             | TypeSynonymSpec TypeSynonymSpec
             | DataTypeSpec DataTypeSpec
             | TypeSpec DataTypeSpec
             | EntitySpec EntitySpec
             | MetaSpec MetaSpec
               deriving (Show)

data TypeSynonymSpec = TypeSynonymDecl Name [FParam] FSort
                       deriving (Show)

data DataTypeSpec = DataTypeDecl Name [FParam] [DataTypeAlt]
                    deriving (Show)

data DataTypeAlt = DataTypeInclusion FSort
                 | DataTypeConstructor Name [FSort]
                   deriving (Eq,Ord,Show)

data EntitySpec = InheritedSpec (Name,FTerm,FSort)
                | MutableSpec (Name,FTerm,FSort) (Name,FPattern,FSort)
                | InputSpec (Name,FPattern,FSort)
                | OutputSpec (Name,FPattern,FSort)
                | ControlSpec (Name,FSort)
                  deriving (Show)

data FunconSpec = FAbbrv FSig (Maybe FTerm) {- nothing if := ... -}
                | FRules FSig [FRule]
                  deriving (Show)

data FRule = FRuleRewrite Name (Maybe [FPattern]) (Maybe FTerm) [FSideCondition]
           | FRuleStep    Name FStep [Either FPremiseStep FSideCondition]
             deriving (Eq,Ord,Show)

data FSideCondition = SCEquality FTerm FTerm
                    | SCInequality FTerm FTerm
                    | SCPatternMatch FTerm FPattern
                    | SCIsInSort FTerm FSort
                      deriving (Eq,Ord,Show)

data FSig = FSig
              { sigName   :: Name,
                sigParams :: [FParam],
                sigSort   :: FSort,
                sigDoc    :: Maybe [CommentPart] 
              }
            deriving (Show)

data CommentPart  = Ordinary String
                  | Asterisk
                  | At String
                  | CommentTerm [Term]
                  | CommentPremise Premise 
                  | SpecInComment CBSSpec
                  deriving Show



type FParam = (ParamPattern, Maybe FSort)

isStrictParam :: FParam -> Bool
isStrictParam param@(_,sorts) = maybe False isStrictSort sorts

isStrictSort :: FSort -> Bool
isStrictSort sort = case sort of
  TSortSeq (TTuple [t]) _ -> isStrictSort t
  TSortSeq t _            -> isStrictSort t
  TSortComputes _         -> False
  TSortComputesFrom _ _   -> False
  _                       -> True

isVariadic :: FParam -> Bool
isVariadic (_, Just (TSortSeq _ _)) = True
isVariadic _ = False

data ParamPattern = PPMetaVar MetaVar
                  | PPSeqMetaVar MetaVar SeqSortOp
                  | PPAny
                  deriving (Eq,Ord,Show)

data FStep = FStep
               { stepSource :: Maybe [FPattern]
               , stepTarget :: FTerm
               , stepInheritedEntities :: [(Name,FPattern)]
               , stepMutableEntities :: ([(Name,FPattern)],[(Name,FTerm)])
               , stepInputEntities :: [(Name,FPattern)]
               , stepOutputEntities :: [(Name,FTerm)]
               , stepControlEntities :: [(Name,FPattern)]
               }
             deriving (Eq,Ord,Show)

data FPremiseStep = FPremiseStep
                      { premiseSource :: FTerm
                      , premiseTarget :: FPattern
                      , premiseInheritedEntities :: [(Name,FTerm)]
                      , premiseMutableEntities :: ([(Name,FTerm)],[(Name,FPattern)])
                      , premiseInputEntities :: [(Name,FTerm)]
                      , premiseOutputEntities :: [(Name,FPattern)]
                      , premiseControlEntities :: [(Name,FPattern)]
                      }
                    deriving (Eq,Ord,Show)

data FPattern = PTuple [FPattern]
              | PList [FPattern]
              | PAnnotated FPattern FSort
              | PADT ADTConstructor [FPattern]
              | PAny
              | PLit FLiteral
              | PMetaVar MetaVar
              | PSeqMetaVar MetaVar SeqSortOp  -- Note: the MetaVar should also contain the operator suffix
                deriving (Eq,Ord,Show)

data FLiteral = FLiteralNat Int
              | FLiteralFloat Double 
              | FLiteralString String
              | FLiteralAtom String
                deriving (Eq,Ord,Show)

type ADTConstructor = String


type FSort = FTerm

type MetaVar = String

data FTerm = TMetaVar MetaVar
           | TLiteral FLiteral
           | TName Name
           | TApp Name [FTerm]
           | TTuple [FTerm]
           | TList [FTerm]
           | TSet [FTerm]
           | TMap [FTerm]
           | TSortPower FTerm FTerm
           | TSortUnion FTerm FTerm
           | TSortInter FTerm FTerm
           | TSortComplement FTerm
           | TSortSeq FTerm SeqSortOp
           | TSortComputes FTerm
           | TSortComputesFrom FTerm FTerm
           | TAny
             deriving (Eq,Ord,Show)

termArgs :: FTerm -> Maybe [FTerm]
termArgs t = case t of 
  TName _    -> Nothing
  TApp _ ts  -> Just ts
  _          -> Nothing

-------------------------------------------------
