{-# LANGUAGE TupleSections #-}

module Print.JavaClasses where

import Funcons.EDSL (Funcons(..), FTerm(..), Values(..), ComputationTypes(..),
                      Types(..))

import Types.FunconModule
import Types.SourceAbstractSyntax (FLiteral(..), SeqSortOp(..), Name)
import Types.CoreAbstractSyntax (Strictness(..), FSig(..),
        FPattern(..), FValSorts(..), FSideCondition(..), EntitySpec(..), CommentPart(..) )
import Types.TargetAbstractSyntax (DataTypeSpec(..), DataTypeAlt(..),)
import Print.Util

import Text.PrettyPrint.HughesPJ
import Data.List.Split (splitOn)
import Data.Char (toUpper)
import Data.Text (unpack)

import System.Directory (createDirectoryIfMissing)
import System.FilePath hiding ((<.>))
import qualified System.FilePath as FP

import CCO.Component

package_name = "sorts.funcons.generated"

data JavaClass = Class  String {-package-} 
                        String {-Class name-} 
                        Doc    {-contents -}

cbs2classes :: FilePath -> Maybe FilePath -> Maybe String -> 
                Component FunconModule (Maybe (IO ())) 
cbs2classes orig_file msrcdir _ = component mycomp 
 where  
  mycomp cbsfile = return $ doPrints allClasses
   where  allClasses =  
            gClasses (funcons cbsfile) ++ 
            concatMap (entityTemplate orig_file) (entities cbsfile) ++
            map (datatypeTemplate orig_file) dspecs ++
            map (gData orig_file) dspecs ++ 
            concatMap (\(DataTypeDecl _ _ alts) -> concatMap (gCons orig_file) alts) dspecs
           where dspecs = datatypes cbsfile 

  doPrints :: [JavaClass] -> Maybe (IO ())
  doPrints [] = Just $ putStrLn "Nothing to generate"
  doPrints cs = Just $ mapM_ doPrint cs
  
  doPrint (Class pack name doc) = case msrcdir of 
    Nothing   -> putStrLn (render doc) >> putStrLn "" 
    Just src  -> do createDirectoryIfMissing True dir
                    writeFile filepath (render doc)
                    putStrLn ("Generated " ++ filepath)
     where  filepath = dir </> name FP.<.> "java"
            dir = src </> package_dir
            package_dir = foldr1 (</>) (splitOn "." pack)

  gClasses :: [FunconSpec] -> [JavaClass]
  gClasses = map gClass

  gClass :: FunconSpec -> JavaClass
  gClass (FunconSpec name sig mdoc rss sss) = 
    Class package_name className 
      (classTemplate orig_file sig className javadoc (gRewrites rss) (gSteps sss)) 
    where className = toClassName name
          javadoc = maybe empty gCommentParts mdoc

                  

classTemplate :: FilePath -> -- source file with funcon def
                  FSig ->    -- signature of the funcon
                  String -> -- classname
                  Doc ->    -- contents of this funcons javadoc
                  Doc ->    -- contents of rewrite function 
                  Doc ->    -- contents of step function
                  Doc       -- full class
classTemplate orig_file fsig className javadoc rewrites steps = 
  text "package" <+> text package_name <> semi $+$
  text ("// GeNeRaTeD FoR: " ++ orig_file) $+$
  vcat (map (\nm -> text "import" <+> text nm <> semi) imports) $+$
  -- class 
  javadoc $+$
  text "public" <+> text "class" <+> text className <+> text "extends Funcons" $+$ 
    codeBlock ( 
      -- constructor
      text "public" <+> text className <> parens arguments $+$ 
        codeBlock (
          text "super" <> parens (strictness (text "fargs")) <> semi
        ) $+$
      -- rewrite()
      text "@Override" $+$
      text "public" <+> text "Funcons" <+> text "rewrite" <> parens rew_args $+$ 
        nest 2 rew_throws $+$
        codeBlock (
          rewrites
        ) $+$
      -- step ()
      text "@Override" $+$
      text "public" <+> text "StepResult" <+> text "step" <> parens step_args $+$ 
        nest 2 step_throws $+$
        codeBlock (
          steps
        )
    )
 where
  arguments | nullary = empty
            | otherwise =  text "Funcons..." <+> text "fargs"
  rew_args | nullary = empty
           | otherwise = text "Funcons[]" <+> text "fargs"
  rew_throws = text "throws" <+> text "EvalException" <> comma <+> text "NoRewriteException"
  step_throws = text "throws" <+> text "EvalException"
  step_args = text "ReadOnly" <+> ro_var 0 <> comma <+> 
              text "ReadWrite" <+> rw_var 0 <> rest
    where rest | nullary = empty
               | otherwise = comma <+> rew_args 
  strictness args = case fsig of 
    FNullary          -> empty 
    FStrict           -> text "Strictness.strict()" <> comma <+> args
    FLazy             -> text "Strictness.lazy()" <> comma <+> args
    FPartiallyLazy ss -> text "Strictness.plazy" <> s_args <> comma <+> args
     where s_args = gTuple $ map op ss
            where op Strict = text "Strictness.strictArg()"
                  op Lazy   = text "Strictness.lazyArg()" 
  nullary = case fsig of  FNullary  -> True
                          _         -> False           

entityTemplate :: FilePath -> EntitySpec -> [JavaClass]
entityTemplate orig_file spec = case spec of
  InheritedSpec nm term -> [mkTemplate "Inherited" nm term]
  MutableSpec nm term   -> [mkTemplate "Mutable" nm term]
  _                     -> []
 where 
  mkTemplate :: Name -> Name -> FTerm -> JavaClass 
  mkTemplate eclass nm term = Class package_name className $ 
    text "package" <+> text package_name <> semi $+$
    text ("// GeNeRaTeD FoR: " ++ orig_file) $+$
    vcat (map (\nm -> text "import" <+> text nm <> semi) imports) $+$
    text "public" <+> text "class" <+> text className $+$ 
    codeBlock ( 
      -- just a field 
      text "static" <+> text "public" <+> text "FValue" <+> text "mydefault" <> 
        gTuple[] <+> text "throws EvalException" $+$
      codeBlock (
        text "try" $+$
          codeBlock (text "return" <+> ppTerm term <.> text "rewrites()" <> semi)$+$
        text "catch" <> gTuple [text "NoRewriteException" <+> text "nr"] $+$
          codeBlock (
            text "System.out.println" <> 
                gTuple [gString ("failed to rewrite default of: " ++ nm)] <> semi $+$
            text "System.exit(1)" <> semi $+$
            text "return" <+> text "null" <> semi
          )
      )
    )
   where  className = eclass ++ toClassName nm          

gRewrites :: [[FRewriteStmt]] -> Doc
gRewrites rrs = snd (
  foldr (try_catch gRewrite) (length rrs,norew) rrs)
  where norew = throwExc "NoRewriteException" [_this] 

gRewrite :: Int -> [FRewriteStmt] -> Doc
gRewrite nro rs = 
  (if nro > 0 then initMetaEnv else empty) $+$
  vcat (map gRewriteStmt rs)

gRewriteStmt :: FRewriteStmt -> Doc
gRewriteStmt stmt = case stmt of
  RewriteTarget fterm -> text "return" <+> ppFuncons fterm <> semi
  ArgsPattern tvar pats -> fsMatch (text tvar) (map ppPattern pats)
  CheckSideCondition cond -> gSideCondition cond <> semi

gSideCondition :: FSideCondition -> Doc
gSideCondition (SCEquality term1 term2) = text "SideConditions" <.>
  text "equality" <> gTuple [_this,ppFuncons term1, ppFuncons term2] 
gSideCondition (SCInequality term1 term2) = text "SideConditions" <.>
  text "inequality" <> gTuple [_this,ppFuncons term1, ppFuncons term2] 
gSideCondition (SCIsInSort term valsort) = text "SideConditions" <.>
  text "isInSort" <> gTuple [_this,ppFuncons term, ppFuncons valsort]
gSideCondition (SCNotInSort term valsort) = text "SideConditions" <.>
  text "isNotInSort" <> gTuple [_this, ppFuncons term, ppFuncons valsort]
gSideCondition (SCPatternMatch term pat) = text env_var <=> text "SideConditions" <.> 
  text "rewritePremise" <> gTuple [_this, ppFuncons term, ppPattern pat, text env_var]

gSteps :: [[FStepStmt]] -> Doc
gSteps sss = 
  snd (foldr (try_catch gStep) (length sss, norule) sss)
 where
    norule = throwExc "NoRuleException" [_this] 

gStep :: Int -> [FStepStmt] -> Doc
gStep nro ss = 
  (if nro > 0 then initMetaEnv else empty) $+$
  text "WriteOnly" <+> wo_var <=> text "new" <+> text "WriteOnly()" <> semi $+$
  vcat (gStepStmts 0 ss) 

gStepStmts :: Int -> [FStepStmt] -> [Doc]
gStepStmts _ [] = []
gStepStmts prem ((PremiseBlock premise):ss) = 
  initPrem (prem + 1) : 
    gStepStmt (prem + 1) premise :
    gStepStmts (prem + 1) ss
gStepStmts prem (s:ss) = gStepStmt prem s : gStepStmts prem ss

initPrem :: Int -> Doc
initPrem prem = 
  text "ReadOnly" <+> ro_var prem <=> ro_var (prem-1) <> semi $+$
  text "ReadWrite" <+> rw_var prem <=> rw_var (prem-1) <> semi

gStepStmt :: Int -> FStepStmt -> Doc
gStepStmt prem stmt = (case stmt of
  PremiseBlock _ -> error "unhandled premise block"
  -- side conditions / pattern-matching
  FRewriteStmt rs -> gRewriteStmt rs
  -- target
  StepTarget term -> text "return" <+> text "new" <+> text "StepResult" <> 
                      gTuple [ppFuncons term, rw_var prem, wo_var] 
  -- premise
  Premise term pat -> 
    text "StepResult" <+> prem_var prem <=>
      parens (ppFuncons term) <.> text "premise" <> 
        gTuple [ro_var prem, rw_var prem] <> semi $+$
    vMatch (prem_var prem <.> text "funcon") (ppPattern pat) $+$
    wo_var <.> text "mappend" <> gTuple [prem_var prem <.> text "wo"] <> semi $+$
    rw_var prem <=> prem_var prem <.> text "rw"
  -- output
  WriteOutput nm term -> 
    wo_var <.> text "output" <.> text "append" <> gTuple [gString nm, ppFuncons term]
  ReceiveOutput nm pat stmt -> 
    gStepStmt prem stmt $+$ -- execute premise first
    text "ListType" <+> var_name nm prem <=> wo_var <.> text "output" <.> 
      text "getWithDefault" <> gTuple [gString nm] <> semi $+$
    vMatch (var_name nm prem) (ppPattern pat)
  -- control 
  WriteControl nm (Just term) -> 
    wo_var <.> text "control" <.> text "append" <> gTuple [gString nm, ppFuncons term]
  WriteControl nm Nothing -> 
    wo_var <.> text "control" <.> text "remove" <> gTuple [gString nm]
  ReceiveControl nm stmt -> 
    gStepStmt prem stmt $+$ -- execute premise first
    text "FValue" <+> var_name nm prem <=> wo_var <.> text "control" <.> 
      text "getWithDefault" <> gTuple [gString nm] <> semi
  -- mutable
  WriteMutable nm term -> writeMutable nm term
  ReadMutable nm pat -> readMutable nm pat
  -- inherited
  ReadInherited nm pat -> text "FValue" <+> var_name nm prem <=>
    ro_var prem <.> text "getWithDefault" <> 
      gTuple [gString nm, defEnt "Inherited" nm] <> semi $+$
    vMatch (var_name nm prem) (ppPattern pat)
  ScopeInherited nm term stmt -> 
    ro_var prem <=> ro_var prem <.> text "put" <> 
      gTuple [gString nm, ppFuncons term] <> semi $+$
    gStepStmt prem stmt 
  ) <> semi
 where  defEnt eclass nm = text (eclass ++ toClassName nm) <.> text "mydefault()"
        readMutable nm pat = text "FValue" <+> var_name nm prem <=> 
          rw_var prem <.> text "getWithDefault" <> 
            gTuple [gString nm, defEnt "Mutable" nm] <> semi $+$
          vMatch (var_name nm prem) (ppPattern pat)
        writeMutable nm term = rw_var prem <=> rw_var prem <.> text "put" <> gTuple
                                [gString nm, ppFuncons term]

gCommentParts :: [CommentPart] -> Doc
gCommentParts cs = text "" -- TODO 
 
prem_var = text . ("premise" ++) . show
ro_var  = text . ("ro" ++) . show
rw_var  = text . ("rw" ++) . show
wo_var  = text "wo0"
var_name nm i = text (replace "-" "_" nm ++ show i)

fsMatch :: Doc {- terms -} -> [Doc] {- patterns-} -> Doc {- pattern-matching -}
fsMatch tvar pats = text env_var <=> text "interpreter.backtracking.patterns.Patterns" <.> text "match" <> gTuple
      ([text env_var, _this, tvar] ++ pats) <> semi

vMatch :: Doc {- term-} -> Doc {- pattern-} -> Doc {- pattern-matching -}
vMatch term pat = text env_var <=> text "interpreter.backtracking.patterns.Patterns" <.> text "match" <> 
                    gTuple [_this, term, pat, text env_var] <> semi

datatypeTemplate :: FilePath -> DataTypeSpec -> JavaClass 
datatypeTemplate orig_file (DataTypeDecl nm _ _) = Class package_name className $
  text "package" <+> text package_name <> semi $+$
  text ("// GeNeRaTeD FoR: " ++ orig_file) $+$
  vcat (map (\nm -> text "import" <+> text nm <> semi) imports) $+$
  text "public" <+> text "class" <+> text className <+> text "extends" <+> text "ADTType"$+$ 
  codeBlock ( 
    -- constructor
    text "public" <+> text className <> gTuple ty_arguments $+$ 
      codeBlock (
        text "super" <> gTuple arguments <> semi
      )
  ) 
 where className = toClassName nm ++ "Type"
       arguments = [text "nm", text "tys", text "cons"]
       ty_arguments = zipWith (<+>) 
                        [text "String", text "Type[]", text "String..."] arguments

gData :: FilePath -> DataTypeSpec -> JavaClass
gData orig_file (DataTypeDecl nm tyargs alts) = Class package_name className $
  classTemplate orig_file FStrict className empty rewrite (gSteps [])
 where rewrite = text "return" <+> text "new" <+> text (className++"Type")<> 
                  gTuple ([gString nm, _this <.> text "argTypes()"] ++ conss) <> semi 
       className = toClassName nm
       conss = concatMap op alts
        where op (DataTypeInclusion _) = []
              op (DataTypeConstructor nm _ _) = [gString nm]

gCons :: FilePath -> DataTypeAlt -> [JavaClass]
gCons _ (DataTypeInclusion _) = []
gCons orig_file (DataTypeConstructor nm args _) = (:[]) $ Class package_name className $
  classTemplate orig_file FStrict className empty rewrite (gSteps [])
 where  className = toClassName nm
        rewrite = text "return" <+> text "new" <+> text "ADTVal" <> 
                    gTuple [gString nm, _this <.> text "argValues()"] <> semi

try_catch :: (Int -> [a] -> Doc) -> [a] -> (Int,Doc) -> (Int,Doc)
try_catch ruler rs (i,rest) = (i-1,) $
  text "// code for step/rewrite rule" <+> text (show i) $+$
  text "try" $+$ -- try this rule
    codeBlock (ruler i rs) $+$
  text "catch" <+> parens (text "EvalException" <+> exc_var) $+$
    codeBlock (
      text "if" <+> parens (exc_var <.> text "failsRule()") $+$ 
        codeBlock rest $+$ -- if fails rule try other rules
        text "else" $+$ --otherwise rethrow exception
        codeBlock (text "throw" <+> exc_var <> semi)
    )
 where exc_var = text $ "ee" ++ show i
        
throwExc :: String -> [Doc] -> Doc
throwExc exc args = text "throw" <+> text "new" <+> text exc <> gTuple args <> semi

initMetaEnv :: Doc
initMetaEnv = text "MetaEnv" <+> text env_var <=> 
                text "new" <+> text "MetaEnv()" <> semi

-- pretty print the term and apply substitution on it
ppFuncons :: FTerm -> Doc
ppFuncons term = ppTerm term <.> text "substitute" <> parens (text env_var)

ppTerm :: FTerm -> Doc
ppTerm term = case term of
  TName nm -> text "new" <+> text (toClassName (unpack nm)) <> parens empty
  TApp nm arg -> text "new" <+> text (toClassName (unpack nm)) <>
    gTuple (ppTermsFromTerm arg) 
  TVar var -> parens (text "new" <+> text "MetaVar" <> parens (gString var))
  TTuple args -> text "new" <+> text "Tuple" <> gTuple (map ppTerm args)
  TMap tups -> text "new" <+> text "MapNotation" <> gTuple (map ppTerm tups)
  TList elems -> text "new" <+> text "List" <> gTuple (map ppTerm elems)
  TSet elems -> text "new" <+> text "Set" <> gTuple (map ppTerm elems)
  TFuncon (FValue v) -> ppValues v
  TFuncon f -> ppTerm (funcons2FTerm f)
  TSortSeq ty op -> text "new" <+> text "TypeSeq" <> gTuple [ppTerm ty, ppSeqOp op]
  TSortUnion ty1 ty2 -> text "new" <+> text "TypeUnion" <> gTuple [ppTerm ty1, ppTerm ty2]
  TSortComputes to -> text "new" <+> text "Computes" <> gTuple [ppTerm to]
  TSortComputesFrom from to -> text "new" <+> text "ComputesFrom" <> 
    gTuple [ppTerm from, ppTerm to]

ppTermsFromTerm :: FTerm -> [Doc]
ppTermsFromTerm (TTuple args) = map ppTerm args
ppTermsFromTerm (TList args)  = map ppTerm args
ppTermsFromTerm term = [ppTerm term]

ppValues :: Values -> Doc
ppValues v = case v of
  Nat n -> text "new" <+> text "sorts.values.Nat" <> gTuple [text (show n)]
  Int i -> text "new" <+> text "sorts.values.Int" <> gTuple [text (show i)]
  String s -> text "new" <+> text "sorts.values.String" <> gTuple [gString s]

ppPattern :: FPattern -> Doc
ppPattern = ppPattern' Nothing

ppPattern' :: Maybe FValSorts -> FPattern -> Doc
ppPattern' mann pat = case pat of
  PAny -> text "new" <+> text "Wildcard" <> mkArgs []
  PLit lit -> text "new" <+> text "PatternValue" <> mkArgs [ppLiteral lit]
  PMetaVar var -> ppPatternVar var Nothing 
  PSeqMetaVar var op -> ppPatternVar var (Just op) 
  PTuple pats -> text "new" <+> text "PatternTuple" <> mkArgs (map ppPattern pats)
  PList pats -> text "new" <+> text "PatternList" <> mkArgs (map ppPattern pats)
  PAnnotated pat valsorts -> ppPattern' (Just valsorts) pat
  PADT con pats -> text "new" <+> text "PatternADT" <> 
    mkArgs ([gString con] ++ map ppPattern pats)
 where ppPatternVar var mop = text "new" <+> text "PatternVar" <>
            mkArgs [text "new" <+> text "MetaVar" <> gTuple var_args]
        where var_args = case mop of
                Nothing -> [gString var]
                Just op -> [gString var, ppSeqOp op]
       mkArgs :: [Doc] -> Doc
       mkArgs args = case mann of Nothing     -> gTuple args
                                  Just vsorts -> gTuple ((ppValSorts vsorts):args)

ppValSorts :: FValSorts -> Doc
ppValSorts (FSequenceValSort term _) = ppTerm term
ppValSorts (FSingletonValSort term) = ppTerm term

ppSeqOp op = (text "SeqOp" <.>) $ case op of
  StarOp          -> text "STAR"
  PlusOp          -> text "PLUS"
  QuestionMarkOp  -> text "QUESTION_MARK"

ppLiteral :: FLiteral -> Doc
ppLiteral (FLiteralNat n) = text "new" <+> text "sorts.values.Nat" <> parens (text (show n))
ppLiteral (FLiteralFloat f) = error "todo: literal float"
ppLiteral (FLiteralAtom char) = error "todo: literal atom"
ppLiteral (FLiteralString str) = text "new" <+> text "sorts.values.String" <>  parens (gString str)

codeBlock :: Doc -> Doc
codeBlock doc = text "{" $+$ nest 2 doc $+$ text "}"

toClassName :: String -> String
toClassName name = className
 where  className = concatMap firstToCap (splitOn "-" name)
        firstToCap []     = []
        firstToCap (hd:tl)= toUpper hd : tl

cast :: String -> Doc -> Doc
cast ty doc = parens (text ty) <+> doc

fullRewrite :: Doc -> Doc
fullRewrite doc = doc <.> text "rewrites()"

_this = text "this"

imports = 
  [ "entities.read.*"
  , "entities.readwrite.*"
  , "entities.write.*"
  , "interpreter.*"
  , "interpreter.backtracking.*"
  , "interpreter.backtracking.patterns.*"
  , "interpreter.exceptions.*"
  , "sorts.funcons.*"
  , "sorts.funcons.Funcons.NoRewriteException"
  -- builtin values
  , "sorts.values.FValue"
  , "sorts.values.MetaVar" 
  , "sorts.values.SeqOp"
  , "sorts.values.Nat"
  , "sorts.values.Int"
  , "sorts.values.Rational"
  , "sorts.values.ADTVal"
  -- builtin types
  , "sorts.values.types.*"
  -- manually defined funcons
  , "sorts.funcons.manual.*"
  ]



