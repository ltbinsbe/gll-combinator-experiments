{-# LANGUAGE LambdaCase #-}
-- many opportunities for small optimisations
-- e.g. do not apply (map text), gList, nameOfSig, stepTypeOfSig, etc. multiple times
module Print.HaskellModule where

import Prelude hiding ((<>),(<$>))

import Funcons.EDSL (Funcons(..),DataTypeMembers(..), f2vPattern)

import Print.Util
import Types.ConcreteSyntax (showConcreteTerm)
import Types.SourceAbstractSyntax hiding (CBSFile(..),CBSSpec(..),FunconSpec(..),FSig,FStep,FPremiseStep,FValueSorts(..),Name,FValueSort(..),EntitySpec(..),FSideCondition(..),DataTypeSpec(..),FTerm(..),DataTypeAlt(..),FValSorts(..),FPattern(..), CommentPart(..))
import Types.CoreAbstractSyntax hiding (Lazy, Strict, CBSFile(..),CBSSPec(..),FunconSpec(..),FRewriteRule(..),FPremiseStep(..),FStep(..),FStepRule(..), DataTypeSpec(..), DataTypeAlt(..))
import qualified Types.CoreAbstractSyntax as C
import Types.FunconModule as F
import Types.TargetAbstractSyntax (InputAccess(..))

import CCO.Component

import Control.Monad (unless)
import Data.Maybe (catMaybes)
import Data.List(intercalate, findIndices)
import Data.List.Split (splitOn)
import Data.Char (toUpper, isUpper, toLower)
import Text.PrettyPrint.HughesPJ
import Data.Text(pack,unpack)

import System.FilePath hiding ((<.>)) 
import qualified System.FilePath as FP
import System.Directory (createDirectoryIfMissing, doesFileExist)

type Name = String
type StepName = Name -- name of a step function

cbs2module :: FilePath -> Maybe FilePath -> Maybe String ->   
                Component FunconModule (Maybe (IO ()))
cbs2module cbsfile msrcdir mlang = component (\cbsfile -> return $
        let mfiledoc = fmap ((gHeader mmodName $+$)) $
                        gFile (aliases cbsfile)
                              (funcons cbsfile)
                              (entities cbsfile)
                              (datatypes cbsfile)
            
        in (fmap doPrint mfiledoc))
 where  render' filedoc = render (text "-- GeNeRaTeD fOr:" <+> text cbsfile $+$ filedoc)
        doPrint doc = case (msrcdir, mlang) of
         (Just srcdir, Just lang) -> do 
            main_exists <- doesFileExist (srcdir </> "Main.hs")
            unless main_exists $ do
              createDirectoryIfMissing False srcdir
              writeFile (srcdir </> "Main.hs") main_contents
              putStrLn "Generated Main.hs"
            createDirectoryIfMissing True hs_file_dir 
            writeFile hs_file (render' doc)
            putStrLn ("Generated " ++ hs_file)
           where  hs_file_dir = srcdir </> foldr (</>) "" hs_file_dir_as_list 
                  hs_file = hs_file_dir </> hs_file_name FP.<.> "hs"
                  main_contents = "import Funcons.Tools (mkMainWithLibraryEntitiesTypes)\n\
                                    \import Funcons." ++ camelcase lang ++ ".Library\n" ++
                                    main_string 
         (Just srcdir, _) -> do 
            writeFile (srcdir </> hs_file_name FP.<.> "hs") (render' doc)
            putStrLn ("Generated " ++ (hs_file_name FP.<.> "hs"))
         _ -> putStrLn (render' doc) --simply print to stdout 
        lang    = maybe "Core" id mlang
        mmodName = case mlang of Nothing  -> Nothing
                                 _        -> Just (intercalate "." modName)
        modName = hsmodNameFromPath lang cbsfile
        hs_file_name = camelcase (takeBaseName cbsfile)
        hs_file_dir_as_list =
             (["Funcons", lang] ++) $
                 map camelcase $ 
                 dropUntil (not . (`elem` roots)) $ 
                 splitDirectories $
                 dropFileName $ 
                 dropExtension cbsfile
        roots = [lang, "Funcons", "Funcons-beta"]

main_string = "main = mkMainWithLibraryEntitiesTypes funcons entities types"

gHeader :: Maybe String -> Doc
gHeader mmodname = vsep $
  [text "{-# LANGUAGE" <+> text "OverloadedStrings" <+> text "#-}"] ++
  (maybe [] (\nm -> [text "module" <+> text nm <+> text "where"]) mmodname) ++
  [text "import" <+> text "Funcons.EDSL"
  ,text "import" <+> text "Funcons.Operations" <+> text "hiding" <+> parens (text "Values" <> comma <> text "libFromList")] ++ 
  (maybe [text "import" <+> text "Funcons.Tools", text main_string] (const []) mmodname)
   
gFile :: AliasMap -> [FunconSpec] -> [EntitySpec] -> [DataTypeMembers] -> Maybe Doc
gFile als fspecs especs dspecs
    | null fspecs && null especs && null dspecs = Nothing
    | otherwise = Just $
    vsep $
        [text fEntities <=> gList [] -- {- defaults have been removed from beta -} 
        ,text fTypes <=> text ftypeEnvFromList $+$
            nest 4 (gList (concatMap (gTypes als) dspecs))
        ,text fFuncons <=> text fLibFromList $+$
            nest 4 (gList lib_entries)]
        ++ map (gStep als) fspecs
--        ++ concatMap (\(DataTypeDecl _ _ alts) -> map gCons alts) dspecs
        ++ map gData dspecs
    where   lib_entries =   concatMap (gLibF als) fspecs 
                        ++  concatMap (gLibD als) dspecs 
--                        ++  concatMap (gLibC als) dspecs

            gLibF :: AliasMap -> FunconSpec -> [Doc]
            gLibF als (F.FunconSpec name sig _ _ _) = 
              [ gTuple [gString alias
                       ,gStepType steptype <+> text (stepName name)]
              | alias <- my_aliases name als ]
                where   steptype = stepTypeOfSig sig

            gLibD :: AliasMap -> DataTypeMembers -> [Doc]
            gLibD als (DataTypeMemberss _ _ []) = []
            gLibD als (DataTypeMemberss nm tyargs _) = 
                [ gTuple [gString alias
                         ,gStepType steptype <+> text (stepName (unpack nm))]
                | alias <- my_aliases (unpack nm) als ]
                where steptype  | null tyargs = Nullary
                                | otherwise   = Strict

gData :: DataTypeMembers -> Doc
gData (DataTypeMemberss nm' tyargs  _) = 
  text (smart_cons_name nm) <=> smart_body $+$
  text sname <+> tyarg_pat <=> main
    where   nm = unpack nm'
            sname = stepName nm
            main = text frewriteType <+> gString nm <+> tyarg
            tyarg_pat | null tyargs = empty
                      | otherwise   = text "ts"
            tyarg | null tyargs = brackets empty
                  | otherwise   = text "ts"
            smart_body 
              | null tyargs = text cFunconName <+> gString nm
              | otherwise   = text cFunconApp <+> gString nm 

{-
gCons :: DataTypeAlt -> Doc
gCons (DataTypeInclusion _) = empty
gCons (DataTypeConstructor nm args strictns) =
  text (smart_cons_name nm) <=> smart_body $+$ 
  text sname <+> args_pat <=> main
    where   args_pat | null args = empty
                     | otherwise = text "fs"
            sname = stepName nm
            main = text fRewritten <+> parens return_val
             where return_val = text cADTVal <+> gString nm <+> arg
                    where arg | null args   = brackets empty
                              | all isStrict strictns = 
                                  parens (text "fvalues" <+> text "fs")
                              | otherwise   = text "fs"
            smart_body = case args of 
                          []  -> text cFunconName <+> gString nm
                          _   -> text cFunconApp <+> gString nm
-}

gStep :: AliasMap -> FunconSpec -> Doc
gStep als fspec@(F.FunconSpec fname fsig mdoc r_rules s_rules) =
    ppMaybeDoc mdoc $+$
    vcat [ text (smart_cons_name name) <+> smart_fargs_var <=> smart_body
         | name <- my_aliases fname als ] $+$
    case steptype of
        Nullary -> text sname <=> main $+$ whereClause
        _ -> text sname <+> text fargs_var <+> text "=" $+$
                nest 4 main $+$
                whereClause
    where   sname           = stepName fname
            steptype        = stepTypeOfSig fsig
            nullary         = case steptype of  Nullary -> True
                                                _       -> False
            smart_fargs_var | nullary   = empty
                            | otherwise = text "fargs"
            smart_body = case steptype of
                Nullary -> text cFunconName <+> gString fname 
                _       -> gFunconApp fname (text fargs_var)


            main | null r_rules && null s_rules = text fNorule <+> selfApp
                                 --TODO ignore rewrites or steps if null
                 | otherwise = text fEvalRules <+> 
                                mkList "rewrite" [1..length r_rules] <+>
                                mkList "step" [1..length s_rules]
             where mkList str = gList . map (\i -> text (str ++ show i))

            args = case steptype of
                    Lazy i is _ -> generateArgs i
                    _           -> error "fargs_var only specified for lazy funcons"

            selfApp = parens $ case steptype of
                        Nullary -> text cFunconName <+> gString fname 
                        Strict  -> gFunconApp fname (parens (text ffvalues <+> text fargs_var))
                        _       -> gFunconApp fname (text fargs_var)

            whereClause | null r_rules && null s_rules = empty
                        | otherwise = nest 4 (text "where" <+> nest 2
                                            (rewriteRules (zip [1..] r_rules) $+$
                                             stepRules (zip [1..] s_rules)))

            rewriteRules :: [(Int, [FRewriteStmt])] -> Doc
            rewriteRules rules = vcat (map rewriteRule rules)
            rewriteRule (idx, stmts) = rule $ initEnv $+$
                            vcat (map (ppRewriteStmt steptype False) stmts)
             where  rule :: Doc -> Doc
                    rule = ppDoBinding (text ("rewrite" ++ show idx)) []

            stepRules :: [(Int, [FStepStmt])] -> Doc
            stepRules rules = vcat (map (stepRule) rules)
            stepRule (idx, stmts) = rule $ initEnv $+$ ppStepStmts steptype stmts
             where
                rule = ppDoBinding (text ("step" ++ show idx)) []

            initEnv = text "let" <+> text env_var <=> text empty_env

ppDoBinding :: Doc -> [Doc] -> Doc -> Doc
ppDoBinding nm args body = nameWithArgs <=> text "do" $$ nest 2 body
  where nameWithArgs = hsep (nm : args)

ppLetDoBinding :: Doc -> [Doc] -> Doc -> Doc
ppLetDoBinding nm args body = text "let" <+> ppDoBinding nm args body

ppBranches rec fnm bs = 
  vcat (zipWith printLet [1..] bs) $+$ 
  text fnm <+> gList (zipWith printCall [1..] bs)
    where printLet i b = ppLetDoBinding (printCall i b) [] 
                          (vcat (map rec b))
          printCall i b = text ("branch" ++ (show i)) <+> text env_var

ppRewriteStmt :: StepType -> Bool -> FRewriteStmt -> Doc
ppRewriteStmt stype lift stmt = case stmt of 
  RBranches bs -> ppBranches (ppRewriteStmt stype False) "rewriteRules" bs
  ArgsPattern _ _ | Nullary <- stype -> empty
  ArgsPattern var pats -> 
    text env_var <<-> text matcher <+> text var <+> ppPatterns pats <+> text env_var
  EnvStore var term       -> 
    text env_var <<-> text envStore <+> gString var <+> parens (ppTerm term) <+> text env_var
  EnvRewrite var -> text env_var <<-> text envRewrite <+> gString var  <+> text env_var
  CheckSideCondition side -> ppSideCondition checker side
      where checker | lift        = lifted_fSideCondition
                    | otherwise   = fSideCondition
  RewriteTarget term  -> text fRewTermTo <+> parens (ppTerm term) <+> text env_var
 where  matcher  | strict, lift = fliftvsMatch
                 | strict       = fvsMatch 
                 | lift         = fliftfsMatch
                 | otherwise    = ffsMatch
        ppPatterns | strict     = ppVPatterns
                   | otherwise  = ppFPatterns
        envRewrite  | lift      = fliftEnvRewrite
                    | otherwise = fEnvRewrite
        envStore    | lift      = fliftEnvStore
                    | otherwise = fEnvStore
        strict = stepTypeStrict stype

ppStepStmts :: StepType -> [FStepStmt] -> Doc
ppStepStmts stype = vcat . map (ppStepStmt stype)

ppStepStmt :: StepType -> FStepStmt -> Doc
ppStepStmt stype = ppStepStmt' True
 where
  ppStepStmt' nocont stmt = case stmt of
    SBranches bs -> ppBranches (ppStepStmt stype) "stepRules" bs
    PremiseBlock s -> ppStepStmt' nocont s
    StepTarget term -> text fStepTermTo <+> parens (ppTerm term) <+> text env_var
    ReadInherited nm pat    -> readInhMut fgetINHPatt nm pat
    ReadInput nm pats       -> readInputs nm pats
    WriteMutable nm term -> writeMutable nm term
    ReadMutable nm pat -> readInhMut fgetMUTPatt nm pat
    WriteOutput nm term     -> writeOutput nm term
    WriteControl nm mterm   -> writeControl nm mterm
    -- these stmts are applied to a continuation
    --  the first of which should receive the env (e.g. env <- ...)
    ScopeInherited nm term cont -> 
      (if nocont then receive_result else id) $ 
        text fWithINHTerm <+> gString nm <+> parens (ppTerm term) <+> 
            text env_var <$> ppStepStmt' False cont
    ScopeInput nm terms acc cont ->  
      (if nocont then receive_result else id) $ 
        text withInput <+> gString nm <+>
            gList (map ppTerm terms) <+> text env_var <$> ppStepStmt' False cont
        where withInput = case acc of  
                            ExactInput -> fwithExactInput
                            ExtraInput -> fwithExtraInput
    ScopeDownControl nm mterm cont -> 
      (if nocont then receive_result else id) $ 
        text fWithCTRLTerm <+> gString nm <+> parens (ppMaybeTerm mterm) <+>
          text env_var <$> ppStepStmt' False cont
    ReceiveControl nms cont | nocont -> 
      gTuple [text env_var, gList (map sig_var nms)] <<-> 
        text "receiveSignals" <+> gList (map gString nms) <$> ppStepStmt' False cont 
                           | otherwise -> error "assert ppStepStmt ReceiveControl"
    ReadControl nm mpat -> 
      (if nocont then receive_result else id) $ 
        text "receiveSignalPatt" <+> sig_var nm <+> 
           parens (ppMVPattern mpat) <+> text env_var 
    ReadDownControl nm mpat -> 
      text env_var <<-> text fgetDCTRLPatt <+> gString nm <+> parens (ppMaybeVPattern mpat) <+> text env_var
    ReceiveOutput nm pat cont -> 
      (if nocont then receive_result else id) $ 
        text freadOUTPatt <+> gString nm<+> 
            parens (ppVPattern pat) <$> ppStepStmt' False cont
    FRewriteStmt stmt       -> ppRewriteStmt stype True stmt
    Premise term pat        -> 
      (if nocont then receive_result else id) $ 
        text fpremise <+> parens (ppTerm term) <+>  
            parens (ppFPattern pat) <+> text env_var
   where receive_result :: Doc -> Doc
         receive_result doc = text env_var <<-> doc

         sig_var sigNm = text ("__var" ++ var2id sigNm)

gTypes :: AliasMap -> DataTypeMembers -> [Doc]
gTypes alt (DataTypeMemberss nm' params []) = []
gTypes als (DataTypeMemberss nm' params alts) =
    [ gTuple [gString alias, gType (DataTypeMemberss (pack alias) params alts)]
    | alias <- my_aliases nm als ]
  where nm = unpack nm'
        gType :: DataTypeMembers -> Doc
        gType = text . show

readInputs :: Name -> [FPattern] -> Doc
readInputs nm pats = vcat (map readInput pats)
    where readInput pat = text env_var <<-> text fmatchInput <+> 
            gString nm  <+> parens (ppVPattern pat) <+> text env_var 

readInhMut :: String -> Name -> FPattern -> Doc
readInhMut entitytype nm pat = text env_var <<-> text entitytype <+> 
    gString nm <+> parens (ppVPattern pat) <+> text env_var

writeMutable :: Name -> FTerm -> Doc
writeMutable nm term = text fputMUTTerm <+> gString nm <+> 
        parens (ppTerm term) <+> text env_var

writeControl :: Name -> (Maybe FTerm) -> Doc
writeControl nm mterm = case mterm of
    Nothing -> empty
    Just term -> text fraiseTerm <+> gString nm <+>
                    parens (ppTerm term) <+> text env_var

writeOutput :: Name -> FTerm -> Doc
writeOutput nm term = text fwriteOUTTerm <+> gString nm <+>
                            parens (ppTerm term) <+> text env_var

ppFuncons :: Funcons -> Doc
ppFuncons f = text (show f)

ppMaybeTerm :: Maybe FTerm -> Doc
ppMaybeTerm = text. show

-- | Sequence operators are ignore in pattern annotations
ppSort :: FTerm -> Doc
ppSort (TSortSeq sort op) = ppSort sort
ppSort term = ppTerm term

ppTerm :: FTerm -> Doc
ppTerm term = text (show term)

ppSideCondition :: String -> FSideCondition -> Doc
ppSideCondition checker sc = text env_var <<-> text checker <+> parens cond <+> text env_var
  where cond = case sc of
            SCEquality term1 term2-> text cSCEquality <+>
                parens (ppTerm term1) <+> parens (ppTerm term2)
            SCInequality term1 term2-> text cSCInequality <+>
                parens (ppTerm term1) <+> parens (ppTerm term2)
            SCIsInSort term1 sort -> text cSCIsInSort <+>
                parens (ppTerm term1) <+> parens (ppTerm sort)
            SCNotInSort term1 sort -> text cSCNotInSort <+>
                parens (ppTerm term1) <+> parens (ppTerm sort)
            SCPatternMatch term pat -> text cSCPatternMatch <+>
                parens (ppTerm term) <+> parens (ppVPattern pat)
            -- We no longer allow this
            -- SCPatternMismatch term pat -> text cSCPatternMismatch <+>
            --     parens (ppTerm term) <+> parens (ppVPattern pat)

ppMaybeDoc :: Maybe [CommentPart] -> Doc 
ppMaybeDoc Nothing      = empty
ppMaybeDoc (Just cs)    = text "-- |" $+$ 
    vcat (map ((text "-- " <>) . text) (lines (concatMap ppCommentPart cs)))

ppCommentPart :: CommentPart -> String
ppCommentPart cp = case cp of 
  Ordinary c        -> c
  Asterisk          -> "*"
  At s              -> "@" ++ s
  CommentTerm ts     -> "`" ++ intercalate "," (map showConcreteTerm ts) ++ "`"
  CommentPremise p  -> "<PREMISE>"
  SpecInComment s   -> "\n" ++ show s ++ "\n"

ppMVPattern :: Maybe FPattern -> Doc
ppMVPattern Nothing = text cNothing
ppMVPattern (Just pat) = text cJust <$> ppVPattern pat 

ppVPattern :: FPattern -> Doc
ppVPattern = text . show . f2vPattern 
 
ppVPatterns :: [FPattern] -> Doc
ppVPatterns pats = gList (map ppVPattern pats)

ppFPatterns :: [FPattern] -> Doc
ppFPatterns pats = gList (map ppFPattern pats)

ppMaybeVPattern :: Maybe FPattern -> Doc
ppMaybeVPattern Nothing = text "Nothing"
ppMaybeVPattern (Just pat) = text "Just" <+> parens (ppVPattern pat) 

ppFPattern :: FPattern -> Doc
ppFPattern = text . show 

-- |
-- Fake a curried smart constructor for the given funcon (name).
-- useful for congruence rules and other helpers that require a
-- smart constructor argument.
gFunconApp :: Name -> Doc -> Doc
gFunconApp nm args = text cFunconApp <+> gString nm <+> parens args

stepName :: Name -> Name
stepName = stepName' . var2id
    where   stepName' "" = error "empty name"
            stepName' (hd:tl) = "step" ++ (toUpper hd : tl)

-- gathering information
data StepType   = Strict
                | Lazy Int [Int] (Maybe Strictness)-- number of args + indices of value-arguments
                | Nullary

stepTypeStrict :: StepType -> Bool
stepTypeStrict Strict = True
stepTypeStrict _      = False

gStepType Strict = text cStrictF
gStepType Nullary = text cNullaryF
gStepType (Lazy args stricts mstrict) 
    | null stricts, Nothing <- mstrict = text cNonStrictF
    | otherwise = text cPartialLazyF <+> gList (map rep [0..args-1])
                    <+> (maybe (text cNonStrict) op mstrict)
    where rep i | i `elem` stricts  = op C.Strict
                | otherwise         = op C.Lazy 
          op C.Strict = text cStrict
          op C.Lazy   = text cNonStrict

stepTypeOfSig :: FSig -> StepType
stepTypeOfSig FStrict = Strict
stepTypeOfSig FLazy = Lazy 0 [] Nothing
stepTypeOfSig FNullary = Nullary
stepTypeOfSig (FPartiallyLazy ss ms) = Lazy (length ss) noncomputing ms
 where noncomputing = findIndices needsCongruence ss

needsCongruence :: Strictness -> Bool
needsCongruence C.Lazy = False
needsCongruence C.Strict = True

hsid :: Name -> Doc
hsid = text . var2id

var2id [] = []
var2id ('-':cs) = '_' : var2id cs
var2id (c:cs) | isUpper c = toLower c : var2id cs
              | otherwise = c : var2id cs

generateArgs :: Int -> [MetaVar]
generateArgs max = foldr op [] [1..max]
 where  op idx terms = ("arg" ++ show idx):terms

smart_cons_name nm =  intercalate "_" (splitOn "-" nm) ++ "_"

-- function names
cType = "Type"
cComps = "ComputationType"
cValue = "FValue"
cFunconName = "FName"
cFunconApp = "FApp"
cTupleNot = "FTuple"
cListNot = "FList"
cMapNot = "FMap"
cSetNot = "FSet"
cStrictF = "StrictFuncon"
cStrict = "Strict"
cNonStrictF = "NonStrictFuncon"
cNonStrict = "NonStrict"
cPartialLazyF = "PartiallyStrictFuncon"
cNullaryF = "NullaryFuncon"
cTupleType = "Tuples"
cFVar = "TVar"
cFApp = "TApp"
cFName = "TName"
cFList = "TList"
cChar = "Char"
cFMap = "FMap"
cFSet = "FSet"
cTFuncon = "TFuncon"
cFSortUnion = "FSortUnion"
cFSortComputes = "FSortComputes"
cFSortComputesFrom = "FSortComputesFrom"
cString = "String"
cFloat = "Float"
cNat = "Nat"
cPValue = "PValue"
cPSeqVar = "PSeqVar"
cPMetaVar = "PMetaVar"
cPWildCard = "PWildCard"
cVPLit = "VPLit"
cVPWildCard = "VPWildCard"
cVPSeqVar = "VPSeqVar"
cPADT = "PADT"
cPList = "PList"
cPTuple = "PTuple"
cVPMetavar = "VPMetaVar"
cPAnnotated = "PAnnotated"
cVPAnnotated = "VPAnnotated"
cSCEquality = "SCEquality"
cSCInequality = "SCInequality"
cSCIsInSort = "SCIsInSort"
cSCNotInSort = "SCNotInSort"
cSCPatternMatch = "SCPatternMatch"
cSCPatternMismatch = "SCPatternMismatch"
cDefMutable = "DefMutable"
cDefInherited = "DefInherited"
cDefInput = "DefInput"
cDefOutput = "DefOutput"
cDefControl = "DefControl"
cFStarOp = "StarOp"
cFPlusOp = "PlusOp"
cFQuestionMarkOp = "QuestionMarkOp"
cADTVal = "ADTVal"
cADTType = "ADT"
cDataTypeMembers = "DataTypeMembers"
--TODO can we use show and read?
cDataTypeInclusion = "DataTypeInclusion"
cDataTypeConstructor = "DataTypeConstructor"

lifted_fSideCondition = "lifted_sideCondition"
fSideCondition = "sideCondition"
fSubsEval = "subsAndRewrite"
fliftfsMatch = "lifted_fsMatch" 
fliftvsMatch = "lifted_vsMatch"
fliftvMatch = "lifted_vMatch" 
fliftvMaybeMatch = "lifted_vMaybeMatch"
ffsMatch = "fsMatch"
fvsMatch = "vsMatch"
fvMatch = "vMatch"
fvMaybeMatch = "vMaybeMatch"
fRewritten = "rewritten"
fRewTo = "rewriteTo"
fRewTermTo = "rewriteTermTo"
fStepTo = "stepTo"
fStepTermTo = "stepTermTo"
fEvalRules = "evalRules"
fNorule = "norule"
fSortErr = "sortErr"
fApplyFuncon = "applyFuncon"
fCongruence = "congruence"
fAfterRewrite = "afterRewrite"
fFuncons= "funcons"
fEntities = "entities"
fTypes = "types"
fLibFromList = "libFromList"
ftypeEnvFromList = "typeEnvFromList"
fIsVal = "isVal"
fHasStep = "hasStep"
fpremise = "premise"
fgetDCTRLPatt = "getControlPatt"
fgetINHPatt  = "getInhPatt"
fgetMUTPatt  = "getMutPatt"
fputMUTTerm  = "putMutTerm"
fWithINHTerm = "withInhTerm"
fWithCTRLTerm = "withControlTerm"
fraiseTerm = "raiseTerm"
fwriteOUTTerm = "writeOutTerm"
freceiveSignalPatt = "receiveSignalPatt"
freadOUTPatt = "readOutPatt"
fTypes_unval = "types_unval"
ffvalues = "map FValue"
fmatchInput = "matchInput"
frewriteType = "rewriteType"
fwithExactInput = "withExactInputTerms"
fwithExtraInput = "withExtraInputTerms"
fliftEnvStore = "lifted_envStore"
fliftEnvRewrite = "lifted_envRewrite"
fEnvStore = "envStore"
fEnvRewrite = "envRewrite"
