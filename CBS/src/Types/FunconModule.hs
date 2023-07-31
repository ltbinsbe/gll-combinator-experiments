
module Types.FunconModule where

import Funcons.EDSL(DataTypeMembers(..))
import Types.SourceAbstractSyntax (Name, MetaVar, AliasMap)
import Types.CoreAbstractSyntax (FSig(..), EntitySpec(..), FPattern(..)
        , FTerm(..), FSideCondition, CommentPart(..), TypeEnv)
import Types.TargetAbstractSyntax (InputAccess)

data FunconModule = FunconModule    { funcons :: [FunconSpec]
                                    , entities :: [EntitySpec]
                                    , datatypes :: [DataTypeMembers]
                                    , env :: TypeEnv
                                    , aliases :: AliasMap }

-- A funcon:
-- * Has a name
-- * Is either strict, lazy or partially lazy
-- * Has a number of rewrite rules (each a sequence of rewrite statements)
-- * Has a number of step rules (each a sequence of step statements)
data FunconSpec = FunconSpec Name FSig (Maybe [CommentPart]) [[FRewriteStmt]] [[FStepStmt]]

-- | Representation of a variable in the target language (Haskell/Java)
type TargetVar = String

fargs_var, env_var, empty_env  :: TargetVar 
empty_env = "emptyEnv"
fargs_var = "fargs"
env_var = "env"

-- an entity value is either:
-- * read       : just ask the monad to get the value
-- * written    : just insert the value into the monad
-- * scoped     : execute further computation with given entity value
-- * received   : what is the value after computation?
data FStepStmt  
        = FRewriteStmt      FRewriteStmt -- subtyping
        | ReadInherited     Name FPattern
        | ScopeInherited    Name FTerm FStepStmt --set inh for the next stmt
        | WriteMutable      Name FTerm 
        | ReadMutable       Name FPattern
        | ReceiveControl    [Name] FStepStmt
        | ReadControl       Name (Maybe FPattern)
        | WriteControl      Name (Maybe FTerm)
        | ReadDownControl   Name (Maybe FPattern)
        | ScopeDownControl  Name (Maybe FTerm) FStepStmt 
        | ReceiveOutput     Name FPattern FStepStmt
        | WriteOutput       Name FTerm 
        | ReadInput         Name [FPattern]
        | ScopeInput        Name [FTerm] InputAccess{-exact?-} FStepStmt
        | PremiseBlock      FStepStmt -- groups statements particular to a premise
        | Premise           FTerm FPattern
        | StepTarget        FTerm 
        | SBranches         [[FStepStmt]]
        deriving (Ord, Eq)

-- subtype of FStepStmt
-- define two evaluation, 1 producing code for rewrite rules, 1 for steps 
--  (applying lifted version of helpers)
data FRewriteStmt    
        = ArgsPattern         TargetVar [FPattern] -- match a sequence of funcons
        | EnvStore            MetaVar FTerm -- bind var to term in the meta-environment
        | EnvRewrite          MetaVar       -- rewrite var inside the meta-environment
        | CheckSideCondition  FSideCondition
        | RewriteTarget       FTerm 
        | RBranches           [[FRewriteStmt]]
        deriving (Ord, Eq)

