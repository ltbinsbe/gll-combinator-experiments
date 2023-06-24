
module Print.Ascii (cbs2ascii)
 where 
import Types.TargetAbstractSyntax (InputAccess(..),DataTypeSpec(..),DataTypeAlt(..))
import Types.FunconModule as F
import Types.SourceAbstractSyntax hiding (CBSFile(..),CBSSpec(..),FunconSpec(..),FSig,FStep,FPremiseStep,FValueSorts(..),Name,FValueSort(..),EntitySpec(..),FSideCondition(..),DataTypeSpec(..),DataTypeAlt(..),FTerm(..),FValSorts(..),FPattern(..))
import Types.CoreAbstractSyntax hiding (Lazy, Strict, CBSFile(..),CBSSPec(..),FunconSpec(..),FRewriteRule(..),FPremiseStep(..),FStep(..),FStepRule(..),DataTypeSpec(..),DataTypeAlt(..))

import Data.List (intersperse)
import Print.Util

import Text.PrettyPrint.HughesPJ

import CCO.Component

cbs2ascii :: FilePath -> Maybe FilePath -> Maybe String ->   
                Component FunconModule (Maybe (IO ()))
cbs2ascii srcfile msrcdir mlang = component (\cbsfile -> return $
        let mfiledoc = gFile srcfile
                        (funcons cbsfile) (entities cbsfile) (datatypes cbsfile)
            doPrint = putStrLn . render
           in fmap doPrint mfiledoc)
         
gFile :: String -> [FunconSpec] -> [EntitySpec] -> [DataTypeSpec] -> Maybe Doc
gFile modname fspecs especs dspecs
    | null fspecs && null especs && null dspecs = Nothing
    | otherwise = Just $
        text "====== Funcons ======" $+$
        text "" $+$
        nest 2 (vcat (map gFuncon fspecs))

gFuncon :: FunconSpec -> Doc
gFuncon (F.FunconSpec nm fsig _ rss sss) = 
        text ("==== " ++ nm ++ "====") $+$
        (if nullary then empty else text "Strictness:" <+> text strictness) $+$
        nest 2 (vsep (map (uncurry gRewriteRule) (zip rss [1..]))) $+$
        text "" $+$
        nest 2 (vsep (map (uncurry gStepRule) (zip sss [1..])))
 where strictness = case fsig of  FStrict   -> "Fully strict"
                                  FLazy     -> "Non-strict"
                                  FNullary  -> ""
                                  FPartiallyLazy sns -> show sns
       nullary = case fsig of FNullary  -> True
                              _         -> False                           

gRewriteRule rs idx = 
        text ("== rewrite rule " ++ show idx) $+$
        nest 2 (vcat (map gRewriteStmt rs))

gStepRule ss idx = 
        text ("== step rule " ++ show idx) $+$
        nest 2 (vcat (map gStepStmt ss)) 

gRewriteStmt (ArgsPattern _ pats) = text "pats" <> gAngle (map gFPattern pats) <> semi
gRewriteStmt (EnvRewrite v)  = text "rewrite(" <> text v <> text ")"
gRewriteStmt (EnvStore v t)  = text v <+> text "|=>" <+> gTerm t
gRewriteStmt (RewriteTarget term) = text "commit" <> gAngle [gTerm term] <> semi
gRewriteStmt (CheckSideCondition sc) = gSideCondition sc <> semi

gStepStmt (FRewriteStmt stmt) = gRewriteStmt stmt
gStepStmt (PremiseBlock stmt) = 
    text "=< premise-block >=" $+$
    nest 2 (gStepStmt stmt)
gStepStmt (Premise term pat) = gTerm term <+> text "--->" <+> gFPattern pat <> semi

gFPattern pat = case pat of
  PTuple pats         -> gTuple (map gFPattern pats) 
  PList pats          -> gList (map gFPattern pats)
  PAnnotated pat ann  -> gFPattern pat <> text ":" <> gValSorts ann
  PADT cons pats      -> text cons <> gTuple (map gFPattern pats)
  PAny                -> text "_"
  PLit lit            -> gLiteral lit
  PMetaVar var        -> text var
  PSeqMetaVar var _   -> text var

gTerm :: FTerm -> Doc
gTerm term = case term of
  TName nm      -> text' nm
  TApp nm term  -> text' nm <> gTerm term
  TVar var      -> text var
  TTuple ts     -> gTuple (map gTerm ts)
  TList ts      -> gList (map gTerm ts)
  _             -> empty

gValSorts ann = case ann of
  FSingletonValSort term    -> gTerm term
  FSequenceValSort term op  -> gTerm term <> ppSortOp op 

gLiteral lit = case lit of
  FLiteralNat i       -> text (show i)
  FLiteralFloat f     -> text (show f)
  FLiteralString str  -> gString str
  FLiteralAtom atom   -> text atom

gSideCondition sc = case sc of
  SCEquality term1 term2    -> gTerm term1 <+> text "==" <+> gTerm term2
  SCInequality term1 term2  -> gTerm term1 <+> text "=/=" <+> gTerm term2
  SCPatternMatch term pat   -> gTerm term <+> text "=" <+> gFPattern pat
  SCIsInSort term ty        -> gTerm term <> colon <> gTerm ty
  SCNotInSort term ty       -> text "~" <+> parens (gTerm term <> colon <> gTerm ty)
