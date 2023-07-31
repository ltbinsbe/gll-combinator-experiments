
module Parsing.Syntax where

import Types.ConcreteSyntax

import Parsing.Mutual

import Parsing.Combinators 

pVarSynName :: Parser VarSynName
pVarSynName = "VAR-SYN-NAME"  
  <:=> VarName <$$> pVarString <** keychar ':' <**> name_lit
  <||> SynName <$$> name_lit

pVarStems :: Parser [VarStem]
pVarStems = "VAR-STEMS"
  <:=> multipleSepBy1 pVarString (keychar ',') <** keychar ':'

pVarStem :: Parser VarStem
pVarStem = "VAR-STEM" <:=> pVarString 

pAlts :: Parser PhraseType
pAlts = "PT-ALTS" <:=> foldr1 PTUnion <$$> multipleSepBy1 pAlt (keychar '|')

pAlt :: Parser PhraseType
pAlt = "SINGLE-PT-ALT" <:=> foldr1 PTSeq <$$> multiple1 pPhraseType

pPhraseType :: Parser PhraseType
pPhraseType = "PHRASE-TYPE"
  <::=> PTSynName <$$> pSynName
  <||>  atom_or_range <$$> atom_lit <**> optional (keychar '-' **> atom_lit)
  <||>  PTComplement <$$ keychar '~' <**> pPhraseType
  <||>  flip ($) <$$> pPhraseType <**> pPhraseTypeRest
  <||>  PTGroup <$$> parens (optional pAlts)
  where atom_or_range a1 (Just a2) = PTRange a1 a2
        atom_or_range a1 Nothing   = PTAtom a1

pPhraseTypeRest :: Parser (PhraseType -> PhraseType)
pPhraseTypeRest = "REST-PHRASE-TYPE"
  <::=> flip PTPostfix  <$$> pPostfix
  <||>  flip PTNoLayout <$$  keychar '_' <**> pPhraseType
