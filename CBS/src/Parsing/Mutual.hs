
module Parsing.Mutual where

import Funcons.EDSL (SeqSortOp(..))

import Parsing.Combinators

import Types.ConcreteSyntax
import Parsing.Lexer (mylexer)

type Parser a = BNF Token a

debug :: Parser a -> String -> [a]
debug p = parseWithOptions [throwErrors] p . mylexer 

-- solves ambiguity B:=>booleans
pDef :: Parser String
pDef = "DEF" <:=> keyword "~>" 

pVar :: Parser Var
pVar = "VAR" <:=> Nothing <$$  keychar '_'
             <||> Just    <$$> alt_id_lit 
             <||> Nothing <$$  keyword "..." 

pVarString :: Parser String
pVarString = "VAR" <:=> (:[]) <$$> keychar '_' <||> alt_id_lit 

pSynName :: Parser String
pSynName = "SYN-NAME" <:=> name_lit

pPostfix :: Parser SeqSortOp 
pPostfix = "POSTFIX"
  <::=> StarOp <$$ keychar '*'
  <||>  PlusOp <$$ keychar '+'
  <||>  QuestionMarkOp <$$ keychar '?'


-- TODO: debug pConst "\"\\\"\""
pConst :: Parser Const
pConst = "CONST"
  <:=>  ConstAtom <$$> atom_lit
  <||>  ConstString <$$> string_lit
  <||>  ConstNat  <$$> int_lit
  <||> ConstFloat <$$> float_lit -- TODO add float_lit to GLL.Combinators

-- tokens
atom_lit :: Parser String
atom_lit = token "ATOM"

name_lit :: Parser String
name_lit = id_lit

bar :: Parser String
bar = token "BAR"

file_name :: Parser String
file_name = token "FILE"

ordinal :: Parser String
ordinal = "NT-ORDINAL" <:=> token "ORDINAL" <||> (show <$$> int_lit)

double_quote :: Parser String
double_quote = token "DQUOTE"
