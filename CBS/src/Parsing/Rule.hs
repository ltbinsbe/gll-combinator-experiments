
module Parsing.Rule where

import Parsing.Syntax
import Parsing.Mutual
import Parsing.Term
import Types.ConcreteSyntax

import Parsing.Combinators

pRuleSpec :: Parser Rule
pRuleSpec = "RULE-SPEC" 
  <:=> keyword "Rule" **> pRule

-- ambiguity:
-- X ---> X atomic(X) ---> V  ------  X ---> V
--    alternative interpretation is X ---> X atomic      (X) ---> V ------- X ---> V
pRule :: Parser Rule
pRule = "RULE" 
  <:=> Inference [] <$$> pConclusion
  <||> Inference <$$> many pPremise <** bar <**> pConclusion
  <||> Desugar <$$> pPhrasePatt <** keychar ':' <**> pPhraseType <** 
                       keychar '=' <**> pPhraseTerm
  <||> Semantics <$$> name_lit  <**> pPhrasePatt <**> optional pTerm <**
                      keychar '=' <**> pTerms

pConclusion :: Parser Conclusion
pConclusion = "CONCLUSION"
  <:=> ConcDynamic <$$> optional pContext <**> pState <**> pDynamic <**> pState
  <||> ConcTyping <$$> optional pContext <**> pState <** keychar ':' <**> pTerm
  <||> ConcStatic <$$> optional pContext <**> pState <** keychar ':' <**> 
                        pTerm <**> pStatic <**> pState
  <||> ConcRewrite <$$> pTerm <** keyword "~>" <**> pTerm

pPremise :: Parser Premise
pPremise = "PREMISE"
  <:=> PremDynamic <$$> optional pContext <**> pState <**> pDynamic <**> pState
  <||> PremTyping <$$> optional pContext <**> pState <** keychar ':' <**> pTerm
  <||> PremStatic <$$> optional pContext <**> pState <** keychar ':' <**> 
                        pTerm <**> pStatic <**> pState
  <||> PremRewrite <$$> pTerm <** keyword "~>" <**> pTerm
  <||> PremEquality <$$> pTerm <** keyword "==" <**> pTerm
  <||> PremInequality <$$> pTerm <** keyword "=/=" <**> pTerm
  <||> PremSubtype <$$> pTerm <** keyword "<:" <**> pTerm

pContext :: Parser Context 
pContext = "CONTEXT"
  <:=> Context <$$> multipleSepBy1 pEntTerm (keychar ',') <** keyword "|-"

pPolarEntTerm :: Parser PolarEntTerm
pPolarEntTerm = "POLAR-ENT-TERM"
  <:=> (\n mp t -> (n,t,mp)) <$$> name_lit <**> optional pPolarity <**> pTerm

pEntTerm :: Parser EntTerm
pEntTerm = "ENT-TERM"
  <:=> (,) <$$> name_lit <**> pTerm 

pPolarity :: Parser Polarity
pPolarity = "POLARITY" <:=> In <$$ keychar '?' <||> Out <$$ keychar '!'

pState :: Parser State
pState = "STATE"
  <:=> StateExplicit <$$ keychar '<' <**> pTerm <** keychar ',' <**>
                         multipleSepBy1 (pEntTerm) (keychar ',') <** keychar '>' 
  <||> StateImplicit <$$> pTerm

pDynamic :: Parser Dynamic
pDynamic = "DYNAMIC"
  <::=> DynamicExplicit <$$ keyword "--" <**> multipleSepBy1 (pPolarEntTerm) (keychar ',') <** keyword "->" <**> optional (int_lit)
  <||> DynamicImplicit <$$ keyword "--" <** keyword "->" <**> optional int_lit
  <||> DynamicComposition <$$> pDynamic <** keychar ';' <**>>> pDynamic

pStatic :: Parser Static
pStatic = "STATIC"
  <:=> StaticExplicit <$$ keyword "==" <**> multipleSepBy1 pPolarEntTerm (keychar ',')
                      <** keyword "=>"
  <||> StaticImplicit <$$ keyword "==" <** keyword "=>"

pArrow :: Parser Arrow
pArrow = "ARROW"
  <:=>  AStatic <$$ keyword "==" <** keyword "=>"
  <||>  ADynamic <$$ keyword "--" <** keyword "->" 

pPred :: Parser Pred
pPred = "PRED"
  <:=> PredType <$$ keychar ':' <**> pTerm
  <||> PredSubType <$$ keyword "<:" <**> pTerm

pPhrasePatt :: Parser PhrasePatt
pPhrasePatt = "PHRASE-PATT"
  <:=> keyword "[[" **> pWordPatts <** keyword "]]"

pWordPatts :: Parser [WordPatt]
pWordPatts = many pWordPatt

pWordPatt :: Parser WordPatt
pWordPatt = "WORD-PATT"
  <::=> WPVar <$$> pVar
  <||>  WPAtom <$$> atom_lit
  <||>  WPGroup <$$> parens pWordPatts
  <||>  parens (WPUnion <$$>  atom_lit <** keychar '|' <**> 
                              manySepBy1 atom_lit (keychar '|'))
