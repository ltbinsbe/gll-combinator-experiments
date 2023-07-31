
module Types.Sequentialisation where

import Types.SourceAbstractSyntax (Name, MetaVar)
import Types.CoreAbstractSyntax (FSig(..), EntitySpec(..), FPattern(..)
        , FTerm(..), DataTypeSpec(..), FSideCondition(..), CommentPart(..), FValSorts(..))
import Types.TargetAbstractSyntax (InputAccess)
import Types.FunconModule(FRewriteStmt(..), FStepStmt(..))

data RRule    = RRule LHS [FSideCondition] FTerm

-- | Representation of a variable in the target language (Haskell/Java)
type TargetVar = String

data LHS      = ValsSPattern TargetVar {- formal parameter in gen. code-} [FPattern]
              | FunconsSPattern TargetVar {- formal parameter in gen. code-} [FPattern] 

data SRule    = SRule LHS Concl FTerm

data Concl    = InhRead Name FPattern Concl
              | Concl2 Concl2

data Concl2   = InpRead Name [MetaVar] Concl2
              | Concl3 Concl3

data Concl3   = MutRead Name FPattern Concl3 FTerm
              | Concl4 Concl4  

data Concl4   = OutWrite Concl4 Name FTerm
              | Bar [Either FSideCondition PBlock]

data PBlock   = InhWrite Name FTerm PBlock
              | PBlock2 PBlock2

data PBlock2  = InpWrite Name [FTerm] InputAccess PBlock2
              | PBlock3 PBlock3

data PBlock3  = MutWrite Name FTerm PBlock4 FPattern
              | PBlock4 PBlock4

data PBlock4  = OutRead PBlock4 Name FPattern
              | SeqPremise FTerm FPattern 

class AccessesEnv a where
  readVars  :: a -> [MetaVar]
  writeVars :: a -> [MetaVar]

instance AccessesEnv FTerm where
  writeVars _ = []
  readVars t0 = case t0 of
    TName _                 -> []
    TFuncon _               -> []
    TVar var                -> [var]
    TApp _ t1               -> readVars t1
    TTuple ts               -> concatMap readVars ts
    TList ts                -> concatMap readVars ts 
    TSet ts                 -> concatMap readVars ts 
    TMap ts                 -> concatMap readVars ts
    TSortSeq t1 _           -> readVars t1
    TSortUnion t1 t2        -> readVars t1 ++ readVars t2
    TSortComputes t1        -> readVars t1
    TSortComputesFrom t1 t2 -> readVars t1 ++ readVars t2 

instance AccessesEnv FPattern where
  writeVars p0 = case p0 of
    PAny                    -> []
    (PLit _)                -> []
    PSeqMetaVar var _       -> [var]
    PMetaVar var            -> [var]
    PTuple ps               -> concatMap writeVars ps 
    PList ps                -> concatMap writeVars ps
    PAnnotated p _          -> writeVars p
    PADT _ ps               -> concatMap writeVars ps
   
  readVars p0 = case p0 of
    PAnnotated _ vs         -> case vs of FSingletonValSort t   -> readVars t
                                          FSequenceValSort t _  -> readVars t
    _                       -> []

instance AccessesEnv a => AccessesEnv (Maybe a) where
  writeVars Nothing   = []
  writeVars (Just a)  = writeVars a
  readVars Nothing    = []
  readVars (Just a)   = readVars a

instance AccessesEnv a => AccessesEnv [a] where
  writeVars           = concatMap writeVars
  readVars            = concatMap readVars 

{- premise blocks are considered one statement wrt sorting 
    if write/read-vars are propagated for `continuation` statements -}
instance AccessesEnv FStepStmt where
  writeVars (FRewriteStmt r)        = writeVars r
  writeVars (ReadInherited _ p)     = writeVars p
  writeVars (ScopeInherited _ t s)  = writeVars t ++ writeVars s 
  writeVars (WriteMutable _ t)      = writeVars t
  writeVars (ReadMutable _ p)       = writeVars p
  writeVars (ReceiveControl _ s)    = writeVars s
  writeVars (ReadControl _ mp)      = writeVars mp 
  writeVars (WriteControl _ mt)     = writeVars mt
  writeVars (ReceiveOutput _ p s)   = writeVars p ++ writeVars s
  writeVars (WriteOutput _ t)       = writeVars t
  writeVars (ReadInput _ pats)      = pats
  writeVars (ScopeInput _ ts _ s)   = writeVars ts ++ writeVars s
  writeVars (PremiseBlock s)        = writeVars s
  writeVars (Premise t p)           = writeVars t ++ writeVars p
  writeVars (StepTarget t)          = writeVars t
  writeVars (SBranches sss)         = writeVars sss 

  readVars (FRewriteStmt r)         = readVars r
  readVars (ReadInherited _ p)      = readVars p
  readVars (ScopeInherited _ t s)   = readVars t ++ readVars s 
  readVars (WriteMutable _ t)       = readVars t 
  readVars (ReadMutable _ p)        = readVars p 
  readVars (ReceiveControl _ s)     = readVars s
  readVars (ReadControl _ mp)       = readVars mp
  readVars (ReceiveOutput _ p s)    = readVars p ++ readVars s
  readVars (WriteOutput _ t)        = readVars t
  readVars (WriteControl _ mt)      = readVars mt
  readVars (ReadInput _ _)          = []
  readVars (ScopeInput _ ts _ s)    = readVars ts ++ readVars s
  readVars (PremiseBlock s)         = readVars s
  readVars (Premise t p)            = readVars t ++ readVars p
  readVars (StepTarget t)           = readVars t 
  readVars (SBranches sss)          = readVars sss 

instance AccessesEnv FRewriteStmt where
  writeVars (RBranches sss)         = writeVars sss
  writeVars (ArgsPattern _ pats)    = writeVars pats
  writeVars (EnvStore v t)          = v : writeVars t
  writeVars (EnvRewrite _)          = []
  writeVars (CheckSideCondition sc) = writeVars sc 
  writeVars (RewriteTarget term)    = writeVars term
  
  readVars (RBranches sss)          = readVars sss
  readVars (ArgsPattern _ pats)     = readVars pats
  readVars (EnvStore _ t)           = readVars t
  readVars (EnvRewrite v)           = [v]
  readVars (CheckSideCondition sc)  = readVars sc
  readVars (RewriteTarget term)     = readVars term

instance AccessesEnv FSideCondition where
  writeVars (SCEquality t1 t2)      = writeVars t1 ++ writeVars t2
  writeVars (SCInequality t1 t2)    = writeVars t1 ++ writeVars t2
  writeVars (SCPatternMatch t p)    = writeVars t ++ writeVars p
  writeVars (SCIsInSort t1 t2)      = writeVars t1 ++ writeVars t2
  writeVars (SCNotInSort t1 t2)     = writeVars t1 ++ writeVars t2

  readVars (SCEquality t1 t2)       = readVars t1 ++ readVars t2
  readVars (SCInequality t1 t2)     = readVars t1 ++ readVars t2
  readVars (SCPatternMatch t p)     = readVars t ++ readVars p
  readVars (SCIsInSort t1 t2)       = readVars t1 ++ readVars t2
  readVars (SCNotInSort t1 t2)      = readVars t1 ++ readVars t2


