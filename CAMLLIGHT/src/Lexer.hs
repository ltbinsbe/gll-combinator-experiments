
module Lexer where

import GLL.Combinators.Lexer
import GLL.Combinators hiding (many, some, Char, optional)

import Text.Regex.Applicative

import Data.Char (isUpper, isLower)
import Data.List ((\\))

cl_lexer :: String -> [Token]
cl_lexer = lexer lexerSettings

lexerSettings = emptyLanguage {
    lineComment         = "//"
  , blockCommentOpen    = "(*"
  , blockCommentClose   = "*)"
  , keywords            = cl_keywords ++ (cl_operators \\ map (:[]) cl_keychars)
  , keychars            = cl_keychars 
  , tokens              = [("CHAR", lCharLit)]
--TODO, ids cannot have adjacent '_' (taken care of by keyword?)
  -- DEVIATION #3
  , identifiers         = lIdentifiers
  , altIdentifiers      = lAltIdentifiers
  }

cl_keywords =  
    ["and"  , "as"    , "begin"     , "do"    , "done"    , "downto"
    ,"else" , "end"   , "exception" , "for"   , "fun"     , "function"
    ,"if"   , "in"    , "let"       , "match" , "mutable" , "not"
    ,"of"   , "or"    , "prefix"    , "rec"   , "then"    , "to"
    ,"try"  , "type"  , "value"     , "where" , "while"   , "with"
    ,"true" , "false" -- DEVIATION #3
    ,"mod" -- DEVIATION #6
    ,"when" -- EXTENSION
    ]

cl_operators = 
    ["#"  , "!" , "!=", "&" , "(" , ")" , "*"   , "*."  , "+"   , "+."
    ,","  , "-" , "-.", "->", "." , ".(", "/"   , "/."  , ":"   , "::"
    ,":=" , ";" , ";;", "<" , "<.", "<-", "<="  , "<=." , "<>"  , "<>."
    ,"="  , "=.", "==", ">" , ">.", ">=", ">=." , "@"   , "["   , "[|"
    ,"]"  , "^" , "_" , "__", "{" , "|" , "|]"  , "}"   , "'"   
    , "**" {- DEVIATION #2 -}
    , "&&", "||" {- EXTENSION equal to "and" and "or" -}
    , ".[" {- EXTENSION, string access -}
    , ".." {- EXTENSION, range pattersn -}
    ]

cl_keychars = ['[', ']', '(', ')', '{', '}']

lCharLit = (:[]) <$ sym '`' <*> charChar <* sym '`'
  where charChar =      sym '\\' *> escaped
                    <|> psym ((/=) '`')
          where escaped =     '\n' <$ sym 'n'
                          <|> '\\' <$ sym '\\'
                          <|> '\t' <$ sym 't'

  -- DEVIATION #3
lIdentifiers :: RE Char String
lIdentifiers = (:) <$> psym isLower <*> idPostfix 

lAltIdentifiers :: RE Char String
lAltIdentifiers = (:) <$> psym isUpper <*> idPostfix

idPostfix :: RE Char String
idPostfix = merge <$> many state1 <*> many (sym '\'')
  where state1 =     (:[]) <$> id_char 
                 <|> (:)   <$> sym '_'  <*> state2
        state2 =     (:[]) <$> id_char
                 <|> (:[]) <$> sym '_' <* empty
        letter = oneOf (['A'..'Z'] ++ ['a' .. 'z'])
        digit  = oneOf  ['0'..'9']
        id_char = letter <|> digit
        merge sss ss =  concat sss ++ ss

{-
idPostfix :: RE Char String
idPostfix = (++) <$> state0 <*> many (sym '\'')
  where state0 =      (:) <$> letter <*> state1 
        state1 =     pure []
                 <|> (:)  <$> id_char <*> state1
                 <|> (:)  <$> sym '_' <*> state2
        state2 =     pure []
                 <|> (:) <$> id_char <*> state1
        letter = oneOf (['A'..'Z'] ++ ['a' .. 'z'])
        digit  = oneOf  ['0'..'9']
        id_char = letter <|> digit
-}
