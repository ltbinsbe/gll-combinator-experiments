{-# LANGUAGE LambdaCase #-}

module Print.Util where

import Prelude hiding ((<>))

import Types.SourceAbstractSyntax (SeqSortOp(..))
import Types.CoreAbstractSyntax

import Data.List (intersperse, intercalate)
import Data.List.Split
import Data.Char (toUpper)
import Data.Text (Text, unpack)
import Text.PrettyPrint.HughesPJ

import Funcons.EDSL (Funcons(..))

import System.FilePath (splitDirectories, dropFileName, dropExtension, takeBaseName)


text' :: Text -> Doc
text' = text . unpack

gList :: [Doc] -> Doc
gList = brackets . hcat . punctuate comma

gTuple :: [Doc] -> Doc
gTuple = parens . hcat . punctuate comma

gAngle :: [Doc] -> Doc
gAngle = angles . hcat . punctuate comma
 where angles d = text "<" <> d <> text ">"

gString :: String -> Doc
gString = doubleQuotes . text

ppSortOp :: SeqSortOp -> Doc
ppSortOp PlusOp = text "+"
ppSortOp StarOp = text "*"
ppSortOp QuestionMarkOp = text "?"

gMaybe :: Maybe Doc -> Doc
gMaybe Nothing = text cNothing
gMaybe (Just d) = text cJust <+> parens d
cNothing = "Nothing"
cJust = "Just"

camelcase :: String -> String
camelcase str = concatMap firstToCap (splitOneOf " -" str)
 where  firstToCap [] = []
        firstToCap (hd:tl) = (toUpper hd):tl

dropUntil :: (a -> Bool) -> [a] -> [a]
dropUntil prop xs = 
    case dropWhile prop xs of
        []  -> xs 
        xs' -> dropUntil prop (tail xs')

replace :: String -> String -> String -> String
replace f t orig = intercalate t (splitOn f orig)

infixl 6 <.>
infixl 6 <$>
infixl 6 <=>
infixl 6 <->>
infixl 6 <<->
d1 <$> d2 = d1 <+> parens d2
d1 <=> d2 = d1 <+> text "=" <+> d2
d1 <->> d2 = d1 <+> text "->" <+> d2
d1 <<-> d2 = d1 <+> text "<-" <+> d2
(<.>) :: Doc -> Doc -> Doc
d1 <.> d2 = d1 <> text "." <> d2
vsep = vcat . intersperse (text "")

{-
termHasVar :: FTerm -> Bool
termHasVar = \case
    TVar _                      -> True
    TName nm                    -> False
    TApp nm term                -> any termHasVar term
    TSeq terms                  -> any termHasVar terms
    TSet terms                  -> any termHasVar terms
    TMap terms                  -> any termHasVar terms
    TList terms                 -> any termHasVar terms
    TFuncon f                   -> False
    TSortSeq term op            -> termHasVar term
    TSortUnion ty1 ty2          -> termHasVar ty1 || termHasVar ty2
    TSortInter ty1 ty2          -> termHasVar ty1 || termHasVar ty2
    TSortComplement ty          -> termHasVar ty
    TSortComputes term          -> termHasVar term
    TSortComputesFrom from to   -> termHasVar from || termHasVar to 
    TAny                        -> False

staticSubstitute :: FTerm -> Funcons
staticSubstitute = \case
    TVar "_"                    -> FValue VAny
    TVar var                    -> error ("failed to apply static substitution to: " ++ var)
    TName nm                    -> FName nm
    TApp nm term                -> FApp nm (map staticSubstitute term)
--    TSeq terms                  -> map staticSubstitute terms
    TSet terms                  -> FSet (map staticSubstitute terms)
    TMap terms                  -> FMap (map staticSubstitute terms)
    TList terms                 -> FList (map staticSubstitute terms)
    TFuncon f                   -> f
    TSortSeq term op            -> FSortSeq (staticSubstitute term) op
    TSortUnion ty1 ty2          -> FSortUnion (staticSubstitute ty1) (staticSubstitute ty2)
    TSortInter ty1 ty2          -> FSortInter (staticSubstitute ty1) (staticSubstitute ty2)
    TSortComplement ty          -> FSortComplement (staticSubstitute ty)
    TSortComputes term          -> FSortComputes (staticSubstitute term)
    TSortComputesFrom from to   -> FSortComputesFrom (staticSubstitute from)
                                                     (staticSubstitute to)
    TAny                        -> FValue VAny
-}

funcons2FTerm :: Funcons -> FTerm
funcons2FTerm = \case
    FName nm                    -> TName nm
    FApp nm term                -> TApp nm (map funcons2FTerm term)
--    FTuple terms                -> TTuple (map funcons2FTerm terms)
    FSet terms                  -> TSet (map funcons2FTerm terms)
    FMap terms                  -> TMap (map funcons2FTerm terms)
--    FList terms                 -> TList (map funcons2FTerm terms)
    FSortSeq term op            -> TSortSeq (funcons2FTerm term) op
    FSortUnion ty1 ty2          -> TSortUnion (funcons2FTerm ty1) (funcons2FTerm ty2)
    FSortInter ty1 ty2          -> TSortInter (funcons2FTerm ty1) (funcons2FTerm ty2)
    FSortComplement ty          -> TSortComplement (funcons2FTerm ty)
    FSortComputes term          -> TSortComputes (funcons2FTerm term)
    FSortComputesFrom from to   -> TSortComputesFrom (funcons2FTerm from)
                                                     (funcons2FTerm to)
    FValue v                    -> TFuncon (FValue v)
    FSortPower ty1 ty2          -> TSortPower (funcons2FTerm ty1) (funcons2FTerm ty2)

hsmodNameFromPath :: String -> FilePath -> [String]
hsmodNameFromPath lang file = hs_file_dir_as_list ++ [hs_file_name] 
 where  hs_file_name = camelcase (takeBaseName file)
        hs_file_dir_as_list =
             (["Funcons", lang] ++) $
                 map camelcase $ 
                 dropUntil (not . (\x -> x `elem` roots)) $ 
                 splitDirectories $
                 dropFileName $ 
                 dropExtension file
        roots = ["Funcons", "Funcons-beta", lang]
