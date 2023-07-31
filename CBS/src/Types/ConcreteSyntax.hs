
module Types.ConcreteSyntax where

import Funcons.EDSL (SeqSortOp(..))

import Data.List (intercalate)

type Name = String

type Var  = Maybe String {- wildcard otherwise -}
showVar Nothing  = "_"
showVar (Just x) = x

type CBSFile = [CBSSpec]

data CBSSpec  = Auxiliary CBSSpec
              | AliasSpec Name Name
              | FunconSpec Name (Maybe Params) Term (Maybe DefRewrite) 
              | TypeSpec Name (Maybe Params) [Bounds] (Maybe DefRewrite) 
              | DatatypeSpec Name (Maybe Params) (Maybe Bounds) [DatatypeAlt]
              | EntitySpec Entity 
              | SyntaxSpec [Prod]
              | LexisSpec [Prod]  
              | SemanticsSpec Name Var PhraseType (Maybe Params) Term (Maybe DefEqual) {- [Rule] -}
              {- RuleSpec and CommentSpec are not necessary for funcon generation
                  however, how to ignore them at parse time without causing ambiguity
                    and possible inefficiency? -}
              | RuleSpec Rule
              | OtherwiseSpec Rule
              | CommentSpec [CommentPart]
              | MetaSpec MetaSpec   
              | MetaVariablesSpec [VarDecl]
              deriving Show

newtype DefRewrite = DefRewrite Term deriving Show
newtype DefEqual   = DefEqual Term deriving Show

data VarDecl  = VarDeclSubType String Term
              | VarDeclType String Term
              deriving Show

data MetaSpec = HS_Imports String {- to be directly copied into a HS module -}
              deriving Show

type Params = [Param]
data Param  = Param Var (Maybe Bounds) 
            deriving Show

data Bounds = InType Type
            | Sub Type
            | Sup Type
            deriving Show

data DatatypeAlt  = Cons Name (Maybe Params)
                  | Inj Var Type 
                  | AltDots
                  deriving Show

type Type = Term
showType    = showConcreteTerm

data Term = TermConst Const 
          | TermVar Var
          | TermDots
          | TermName Name
          | NameApp Name Term
          | VarApp Var Term
          | Typed Term Type
          | Computes Type
          | ComputesFrom Type Type
          | TermPostfix Type SeqSortOp 
          | TermSequence [Term] -- wrapped inside 'group'
          | TermComplement Term
          | TermUnion Type Type
          | TermInter Type Type
          | TermTuple [Term]
          | TermList [Term]
          | TermSet [Term]
          | TermMap [Maybe (Term, Term)] --nothing when "..."
          | TermPower Term Term
          -- semantic translation
          | SemanticsApp Name PhraseTerm (Maybe Term)
          deriving Show

-- | Smart constructor to replace `TermTuple` that prevents singleton tuples
termTuple :: [Term] -> Term
termTuple [t] = t
termTuple ts  = TermTuple ts

termName :: Term -> Name
termName (NameApp nm _) = nm
termName (TermName nm) = nm
termName t = error ("termName: " ++ show t)

termArgs :: Term -> Maybe [Term]
termArgs (NameApp nm arg) = case arg of
  TermTuple []    -> Nothing
  TermTuple args  -> Just args
  _               -> Just [arg]
termArgs _ = Nothing
  
data Const  = ConstAtom String
            | ConstString String
            | ConstNat Int
            | ConstFloat Double 
            deriving Show

showConst c =  case c of 
  ConstAtom str     -> "'" ++ str ++ "'"
  ConstString  str  -> show str
  ConstNat  i       -> show i
  ConstFloat d      -> show d

showConcreteTerm :: Term -> String
showConcreteTerm t = case t of 
  TermConst c                 -> showConst c
  TermVar x                   -> showVar x
  TermDots                    -> "..."
  TermComplement t2           -> "~" ++ showConcreteTerm t2
  TermName n                  -> n
  NameApp n t2                -> n ++ showConcreteTerm t2
  VarApp x t2                 -> showVar x ++ showConcreteTerm t2
  Typed t2 ty                 -> showConcreteTerm t2 ++ ":" ++ showType ty
  Computes ty                 -> "=>" ++ showType ty
  ComputesFrom fty tty        -> showType fty ++ "=>" ++ showType tty
  TermPostfix ty op           -> showType ty ++ show op
  TermSequence seq            -> intercalate "," (map showConcreteTerm seq)
  TermUnion t1 t2             -> showConcreteTerm t1 ++ "|" ++ showConcreteTerm t2
  TermInter t1 t2             -> showConcreteTerm t1 ++ "&" ++ showConcreteTerm t2
  TermTuple ts                -> "(" ++ showConcreteTerm (TermSequence ts) ++ ")"
  TermList ts                 -> "[" ++ showConcreteTerm (TermSequence ts) ++ "]"
  TermSet ts                  -> "{" ++ showConcreteTerm (TermSequence ts) ++ "}"
  TermMap mkvs                -> "{" ++ intercalate "," (map showMKV mkvs) ++ "}"
  TermPower t1 t2             -> showConcreteTerm t1 ++ "^" ++ showConcreteTerm t2
  SemanticsApp nm sxs Nothing -> nm ++ "[[" ++ concatMap showPhraseTerm sxs ++ "]]"
  SemanticsApp nm sxs (Just ty2) -> showConcreteTerm (SemanticsApp nm sxs Nothing) ++ 
                                    "(" ++ showConcreteTerm ty2 ++ ")" 
  where
    showMKV mkv = case mkv of 
      Nothing       -> "..."
      Just (k, v)   -> showConcreteTerm k ++ "|->" ++ showConcreteTerm v

data Rule = Inference [Premise] Conclusion
          -- semantics
          | Desugar PhrasePatt PhraseType PhraseTerm
          | Semantics Name PhrasePatt (Maybe Term) [Term]
          deriving Show

type PhrasePatt = [WordPatt]
type PhraseTerm = [WordTerm]
data PhraseType = PTSynName Name
                | PTAtom Atom 
                | PTRange Atom Atom
                | PTPostfix PhraseType SeqSortOp
                | PTComplement PhraseType 
                | PTSeq PhraseType PhraseType
                | PTNoLayout PhraseType PhraseType
                | PTUnion PhraseType PhraseType
                | PTGroup (Maybe PhraseType)
                deriving (Show)

data WordTerm   = WTVar Var 
                | WTAtom String
                | WTGroup [WordTerm]
                deriving (Show)

data Premise    = PremDynamic (Maybe Context) State Dynamic State
                | PremTyping (Maybe Context) State Term
                | PremStatic (Maybe Context) State Term Static State
                | PremRewrite Term Term
                | PremEquality Term Term
                | PremInequality Term Term
                | PremSubtype Term Term
                deriving (Show)

premSource :: Premise -> Term 
premSource (PremRewrite t1 _) = t1
premSource (PremStatic _ s _ _ _) = stateTerm s
premSource (PremTyping _ s _) = stateTerm s
premSource (PremDynamic _ s _ _) = stateTerm s
premSource (PremEquality t _) = t
premSource (PremInequality t _) = t
premSource (PremSubtype t _) = t

premTarget :: Premise -> Term 
premTarget (PremRewrite _ t) = t
premTarget (PremStatic _ _ _ _ s) = stateTerm s
premTarget (PremTyping _ _ t) = t -- type
premTarget (PremDynamic _ _ _ s) = stateTerm s
premTarget (PremEquality _ t) = t
premTarget (PremInequality _ t) = t
premTarget (PremSubtype _ t) = t

data Conclusion = ConcDynamic (Maybe Context) State Dynamic State
                | ConcTyping (Maybe Context) State Term
                | ConcStatic (Maybe Context) State Term Static State
                | ConcRewrite Term Term
                deriving (Show)

concSource :: Conclusion -> Term 
concSource (ConcRewrite t1 _) = t1
concSource (ConcStatic _ s _ _ _) = stateTerm s
concSource (ConcTyping _ s _) = stateTerm s
concSource (ConcDynamic _ s _ _) = stateTerm s

concTarget :: Conclusion -> Term 
concTarget (ConcRewrite _ t) = t
concTarget (ConcStatic _ _ _ _ s) = stateTerm s
concTarget (ConcTyping _ _ t) = t -- type
concTarget (ConcDynamic _ _ _ s) = stateTerm s

data State      = StateExplicit Term [EntTerm]
                | StateImplicit Term
                deriving (Show)

stateTerm :: State -> Term
stateTerm (StateExplicit t _) = t
stateTerm (StateImplicit t) = t

stateEnts :: State -> [EntTerm]
stateEnts (StateExplicit _ es) = es
stateEnts (StateImplicit _) = []

data Dynamic    = DynamicExplicit [PolarEntTerm] (Maybe Int) -- premise id
                | DynamicImplicit (Maybe Int) --premise id
                | DynamicComposition Dynamic Dynamic
                deriving Show

dynamicEnts :: Dynamic -> [PolarEntTerm]
dynamicEnts (DynamicExplicit ps _) = ps
dynamicEnts _ = []

data Static     = StaticExplicit [PolarEntTerm]
                | StaticImplicit 
                deriving Show

data WordPatt   = WPVar Var 
                | WPAtom String
                | WPGroup [WordPatt]
                | WPUnion Atom [Atom]
                deriving (Show)
            
type Atom = String

showPhraseTerm :: WordTerm -> String
showPhraseTerm wt = case wt of 
  WTVar x     -> showVar x
  WTAtom a    -> "'" ++ a ++ "'"
  WTGroup wts -> "(" ++ concatMap showPhraseTerm wts ++ ")" 

data Entity   = EntContextual Ent Arrow
              | EntMutable Ent Arrow Ent
              | EntObservable EntArrow
              deriving Show

data Arrow    = ADynamic | AStatic 
              deriving Show
data EntArrow = EADynamic Ent | EAStatic Ent
              deriving Show

type EntTerm  = (Name, Term)
type PolarEntTerm = (Name, Term, Maybe Polarity)

data Ent      = EntVarStem VarStem (Maybe Polarity)
              | EntName Name (Maybe Polarity) Var Term
              deriving Show
  
data Polarity = In | Out  
              deriving (Show, Enum) 

data Context  = Context [EntTerm] deriving Show

contextEnts :: Maybe Context -> [EntTerm]
contextEnts = maybe [] (\(Context es) -> es)

data Pred     = PredType Term
              | PredSubType Term
              deriving Show

data CommentPart  = Ordinary String
                  | Asterisk
                  | At String
                  | CommentTerm [Term]
                  | CommentPremise Premise
                  | SpecInComment CBSSpec
                  deriving Show


showComments :: [CommentPart] -> String
showComments = concatMap showComment

showComment :: CommentPart -> String
showComment (Ordinary c) = c
showComment (Asterisk) = "*"
showComment (At sect) = "@" ++ sect
-- TODO should use showFuncons, but requires static substitute + simplification
showComment (CommentTerm t) = "`" ++ show t ++ "`"
showComment c = "<missing comment-part>"


data Prod = Prod [VarStem] SynName PhraseType -- lists of alternatives
          | SDFComment [CommentPart]
          deriving Show

type VarStem    = String
type SynName    = String
data VarSynName = VarName VarStem SynName 
                | SynName String
                deriving Show


