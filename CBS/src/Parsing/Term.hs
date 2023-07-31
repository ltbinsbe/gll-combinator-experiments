
module Parsing.Term where

import Parsing.Mutual
import Types.ConcreteSyntax

import Parsing.Combinators

pType :: Parser Type
pType = "TYPE" <:=> pTerm

-- ambiguity:
-- S=>T (alternative interpretation S applied to =>)
pTerm :: Parser Term 
pTerm = "TERM"
  <::= SemanticsApp <$$> name_lit <**> pPhraseTerm <**> optional pTerm
  <||> TermConst <$$> pConst
  <||> TermVar <$$> pVar 
  <||> TermDots <$$ keyword "..."
  <||> TermName <$$> name_lit
  -- ambiguity "X:T,Y:T" (non-associative, no nesting)
  <||> Typed <$$> pTerm <** keychar ':' <**> pType
  <||> Computes <$$ keyword "=>" <**> pType
  <||> ComputesFrom <$$> pType <** keyword "=>" <**> pType  
  <||> TermComplement <$$ keychar '~' <**> pTerm
  <||> TermPostfix <$$> pType <**> pPostfix
  <||> TermUnion <$$> pTerm <** keychar '|' <**>>> pTerm
  <||> TermInter <$$> pTerm <** keychar '&' <**>>> pTerm 
  <||> termTuple <$$ keychar '(' <**> pTerms <** keychar ')'
  <||> TermList <$$ keychar '[' <**> pTerms <** keychar ']'
  <||> TermSet <$$ keychar '{' <**> pTerms <** keychar '}'
  <||> TermMap <$$ keychar '{' <**> pPoints <** keychar '}'
  <||> TermPower <$$> pTerm <** keychar '^' <**> pTerm
--  <||> pTermSeq {- replaced by specific occurrence as rhs of semantics spec -}
  <||> NameApp <$$> name_lit <**> pTerm
  <||> VarApp <$$> pVar <**> pTerm
  <||> double_quote **> pTerm <** double_quote
{-
pTermSeq :: Parser Term
pTermSeq = "TERMS" <::=> 
  merge <$$> pTerm <**> optional (keychar ',' **> pTermSeq)
  <||> satisfy (TermSequence [])
 where  merge t (Just (TermSequence ts)) = TermSequence (t:ts)
        merge t1 (Just t2) = TermSequence [t1,t2]
        merge t1 Nothing = t1
-}
-- obvious ambiguity (associativity)
-- 1,2,3 (why does manySepBy2 not resolve this?)
pTermSeq :: Parser Term
pTermSeq = "TERMSEQ" <:=> shortest_match (TermSequence <$$> multipleSepBy2 pTerm (keychar ','))

-- obvious ambiguity (associativity)
-- 1,2,3 (why does manySepBy2 not resolve this?)
-- TODO generalise type argument of first parameter of rassoc?
pTerms :: Parser [Term]
pTerms = "TERMS" <:=> shortest_match (manySepBy pTerm (keychar ',') <** satisfy ())

pTermUnions :: Parser [Term]
pTermUnions = "TERMUNIONS" <::=> 
  (:) <$$> pType <** keychar '|' <**> pTermUnions0 
 where pTermUnions0 = "0TERMUNIONS" <:=>
                        (:[]) <$$> pType
                        <||> pTermUnions

pTermInters :: Parser [Term]
pTermInters = "TERM-INTERS" <::=> 
  (:) <$$> pType <** keychar '&' <**> pTermInters0 
 where pTermInters0 = "0TERM-INTERS" <:=>
                        (:[]) <$$> pType
                        <||> pTermInters


{-
pTermUnions :: Parser [Term]
pTermUnions = "TERMUNIONS" <:=> multipleSepBy1 pType (keychar '|')
-}

-- | Key-Value pairs of terms in a map
-- pair is optional, can be given as ...
pPoints :: Parser [Maybe (Term, Term)]
pPoints = "POINTS" <:=> multipleSepBy1 pPair (keychar ',')
 where  pPair :: Parser (Maybe (Term, Term))
        pPair = "PAIR"  <:=> (Just .) . (,) <$$> pTerm <** keyword "|->" <**> pTerm
                        <||> Nothing <$$ keyword "..."

pPhraseTerm :: Parser PhraseTerm
pPhraseTerm = "PHRASE-TERM"
  <:=> keyword "[[" **> pWordTerms <** keyword "]]"

pWordTerms :: Parser [WordTerm]
pWordTerms = many pWordTerm 

pWordTerm :: Parser WordTerm
pWordTerm = "WORD-TERM"
  <::=> WTVar <$$> pVar
  <||>  WTAtom <$$> atom_lit
  <||>  WTGroup <$$> parens pWordTerms
