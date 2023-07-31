
module Parsing.Lexer (Parsing.Lexer.lexer, mylexer) where

import Parsing.Combinators (Token(..),SubsumesToken(..))

import CCO.Component

import Data.Char (isDigit, isAlpha, isUpper, isLower, isAlphaNum, isSpace)
import Text.Regex.Applicative
import Text.Read (readEither)

lexer :: Component String [Token]
lexer = component (return . mylexer)
--lexer = component (((\x -> trace (show x) (return x))) . mylexer)

mylexer = sSpecs

-- Do not forget that states can be created that do not perform
-- longest match by default. Could help to disambiguate atoms for example.
lState :: String -> Bool -> RE Char t -> (t -> String -> [Token]) -> 
                  (t -> Maybe Token) -> String -> [Token]
lState _ _ _ _ _ [] = []
lState stateName discardLayout myTokens mySelector adder s =
    let re | discardLayout = Just <$> myTokens <|> ws
           | otherwise     = Just <$> myTokens
        ws =      (Nothing <$ some (psym isSpace))
              <|> (Nothing <$ string "//" <* many (psym ((/=) '\n')))
              <|> (Nothing <$ string "#" <* many (psym ((/=) '\n')))
    in case findLongestPrefix re s of
        Just (Just tok, rest)   -> (maybe id (:) (adder tok)) (mySelector tok rest)
        Just (Nothing,rest)     -> lState stateName discardLayout myTokens mySelector adder rest
        Nothing                 -> error ("lexical error at " ++ stateName ++ ": " ++ show (take 10 s))


sSpecs = lState "SPECS" True (lCommentStart <|> lTokens) sel Just
  where sel tok = case tok of  Keyword "/*"           -> sComment
                               Keyword "/*HS-IMPORTS" -> sComment
                               Keyword "Section"      -> sSectionNum
                               Keyword "Subsection"   -> sSectionNum
                               _                      -> sSpecs

sSectionNum = lState "SECTION-NUM" True (optional lSectNum) sel id
  where sel tok = sSection 

sSection = lState "SECTION" False lTitleWords (const sSpecs) Just

sComment = lState "COMMENT" False 
              (lHS_import <|> lTick <|> lCommentEnd <|> lCommentPart) sel Just
  where sel tok = case tok of Token "TICK" _  -> sTickIn 
                              Keyword "*/"    -> sSpecs
                              _               -> sComment
        lHS_import = Keyword <$> string "HS-IMPORTS"

sTickIn = lState "TICK-IN" True (lTick <|> lTokens) sel Just
  where sel tok = case tok of Token "TICK" _  -> sTickIn
                              _               -> sSpecInTick

sTickOut = lState "TICK-OUT" False (lTick <|> lCommentPart) sel Just
  where sel tok = case tok of Token "TICK" _  -> sTickOut
                              _               -> sComment

sSpecInTick = lState "SPEC-IN-TICK" True (lTick <|> lTokens) sel Just
  where sel tok = case tok of Token "TICK" _  -> sTickOut
                              _               -> sSpecInTick


lTokens :: SubsumesToken t => RE Char t
lTokens =
        lCharacters
    <|> lKeywords
    <|> charsToInt  <$> optional (sym '-') <*> some (psym isDigit)
    <|> upcast . IDLit . Just <$> lName 
    <|> upcast . AltIDLit . Just <$> lVar 
--    <|> upcast . CharLit . Just <$> lCharLit
    <|> upcast . StringLit . Just <$> lStringLit
    <|> lMore
    where
            charsToInt Nothing n = upcast (IntLit (Just (read n)))
            charsToInt (Just _) n = upcast (IntLit (Just (-(read n))))

            lChar c = upcast (Char c) <$ sym c
            lCharacters = foldr ((<|>) . lChar) empty cbs_characters

            lKeyword k  = upcast (Keyword k) <$ string k
            lKeywords = foldr ((<|>) . lKeyword) empty cbs_keywords

            lMore = foldr ((<|>) . uncurry lToken) empty myTokens 
            lToken t re = upcast . Token t . Just <$> re

            lStringLit = toString <$ sym '\"' <*> many strChar <* sym '\"'
             where strChar =  sym '\\' *> sym '\"'
                              <|> psym ((/=) '\"')
                   toString inner = case readEither ("\"" ++ inner ++ "\"") of
                      Left _  -> inner
                      Right v -> v 

            lCharLit = id <$ sym '\'' <*> charChar <* sym '\''
              where charChar = sym '\\' *> sym '\''
                                <|> psym ((/=) '\'')

cbs_characters = "~():,*+?!|[]{}.@=<>-_&^"

cbs_keywords =  [ "Alias"
                , "Assert"
                , "Auxiliary"
                , "Built-in"
                , "Datatype"    
                , "Entity"                
                , "Funcon"
                , "Hidden"
                , "Language"
                , "Lexis"
                , "Meta-variables"
                , "Otherwise" 
                , "Rule"
                , "SDF"
                , "Semantics"
                , "Syntax"
                , "Type"
                , "Variables"
                , "...", ">:", "<:", "=>", "|->", "==", "~>" 
                , "=/=", "|-", "--", "->", "::=", "[[", "]]"]

lCommentStart = Keyword "/*" <$ sym '/' <* sym '*'
            <|> Keyword "/*HS-IMPORTS" <$ string "/*HS-IMPORTS"
lCommentEnd   = Keyword "*/" <$ sym '*' <* sym '/'

myTokens =  [("ATOM", lAtom), ("FILE", lFile), ("BAR", lBar)
            ,("ORDINAL", lOrdinal), ("DQUOTE", lDQuote) ]

lDQuote = "\\\"" <$ sym '\\' <* sym '\"'

lBar = "----" <$ sym '-' <* sym '-' <* sym '-' <* sym '-' <* many (sym '-')

lName = (:) <$> psym isLower <*> many (psym (\c -> isAlphaNum c || c == '-'))

lCommentPart :: SubsumesToken t => RE Char t
lCommentPart = 
      upcast (Char '*') <$ sym '*'
  <|> upcast (Char '@') <$ sym '@'
  <|> upcast <$ sym '@' <*> lSectNum
  <|> upcast . Token "ORDINARY" . Just <$> lOrdinary
                

lOrdinary = some $ psym (\c -> c /= '*' && c /= '`' && c /= '@')

--TODO atoms are not being lexed correctly
-- for example '\' | '`' should be two atoms separated by a char '|'
-- this is an interesting example of ambiguity
--
-- ambiguity: '\' '\' , one atom '\' ' followed by \', or two atoms '\'
--
-- Lexis
--    capitalized-characters ::= '\' | '`' 
lAtom = sym '\'' *> ((concat <$> few atom_char) <|> lBackslash <|> escaped) <* sym '\''
  where atom_char = (:[]) <$> psym (not . invC)
-- TODO how to allow escaped single quotes in atoms (see ambiguities above)
--                      <|> escaped 
         where invC c = c == '\'' || c == '\t' || c == '\n' || c == '\r'  
 --                           || c == '|' {- temporary fix -}

        escaped = (\a b -> [a,b]) <$> sym '\\' <*> sym '\''
lVar = (\c xs ys zs -> c:xs++ys++zs) <$> psym isUpper <*> many (psym isAlpha) 
            <*> stem_rest <*> rest
  where stem_rest = (++) <$> (concat <$> many ((:) <$> sym '-' <*> some (psym isAlpha))) 
                      <*> stem_suffix
        stem_suffix = maybe [] id <$> optional ((\a b -> [a,b]) <$> sym '-' <*> psym isDigit)
        rest = (++) <$> suffix <*> (maybe [] id <$> (optional postfix))
         where suffix = (++) <$> many (psym isDigit) <*> many (sym '\'')
               postfix = (:[]) <$> (sym '*' <|> sym '+' <|> sym '?')

lFile = ((++)) . concat <$> many part_sep <*> part
 where part = some (psym isAlphaNum)
       part_sep = (\a b -> a ++ [b]) <$> part <*> (sym '-' <|> sym '_')

lSectNum :: RE Char Token
lSectNum =    Token "SECT-NUM" . Just <$> lSect1Num 
          <|> Token "SECT-NUM" . Just <$> lSect2Num 
          <|> Token "SECT-NUM" . Just <$> lSect3Num 
          <|> Token "SECT-NUM" . Just <$> lSect4Num 

-- ambiguity MISC lexes both as lSect1Num, but should be interpreted as lTitleWords
lSect1Num = lOrdinal
lSect2Num = (\x y z -> x++[y]++z) <$> lOrdinal <*> sym '.' <*> lOrdinal
lSect3Num = (\x1 x2 x3 x4 x5 -> x1++[x2]++x3++[x4]++x5) <$> 
              lOrdinal <*> sym '.' <*> lOrdinal <*> sym '.' <*> lOrdinal 
lSect4Num = (\x1 x2 x3 x4 x5 x6 x7 -> x1++[x2]++x3++[x4]++x5++[x6]++x7) <$> 
              lOrdinal <*> sym '.' <*> lOrdinal <*> sym '.' <*> lOrdinal 
                       <*> sym '.' <*> lOrdinal
lOrdinal = some (psym isDigit) {- CAUSES AMBIGUITY, IS IT USED? <|> (:[]) <$> psym isAlpha-}

lTitleWords :: RE Char Token
lTitleWords = Token "TITLE" . Just <$> many (psym ((/=) '\n')) <* sym '\n' 

lTick :: SubsumesToken t => RE Char t
lTick = upcast (Token "TICK" (Just "`")) <$ sym '`'

-- | Escaped backslash
lBackslash = "\\" <$ sym '\\' <* sym '\\'

concatMany :: RE Char String -> RE Char String
concatMany p = concat <$> many p 

concatSome p = concat <$> some p

{-
notFollowedBy :: RE c s1 -> RE c s2 -> RE c s1
notFollowedBy p q = do
  -- apply the regex p
  (res, matched) <- withMatched p
  case match q of --then see if the regex q matches
    Just _  -> -- if it does we need to insert `matched` back into the input string
               empty
    Nothing -> return res -- otherwise just return the result
-}


