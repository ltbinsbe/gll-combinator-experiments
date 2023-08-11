{-# LANGUAGE TupleSections #-}

module Parsing.Spec where

import Parsing.Term
import Parsing.Mutual
import Parsing.Rule
import Parsing.Syntax
import Types.ConcreteSyntax

import CCO.Component

import Parsing.Combinators hiding (Prod)

parser :: Component [Token] [CBSFile]
-- parser = component (return . evaluatorWithParseDataAndOptions [strictBinarisation] [throwErrors] pCBS)
--parser = component (return . evaluatorWithParseDataAndOptions [noSelectTest,strictBinarisation] [throwErrors] pCBS)
parser = component (return . evaluatorWithParseDataAndOptions [] [throwErrors] pCBS)

pCBS :: Parser CBSFile
pCBS = "CBS-FILE"
  <:=> optional (keyword "Language" <** string_lit) **> pManySpecs

pManySpecs :: Parser [CBSSpec]
pManySpecs = "MANY-SPECS"
  <::=> (:) <$$> pComment <**> pManySpecs      --comments
  <||>  id  <$$  keyword "Assert" <** pPremise <**> pManySpecs -- discard assertions
  <||>  id  <$$ keyword "Built-in" <** pSpec <**> pManySpecs -- ignore built-ins
  <||>  (:) <$$> pSpec <**> pManySpecs
  <||>  id <$$ brackets (multiple pRef) <**> pManySpecs
  <||>  satisfy []

pRef :: Parser String
pRef = "RefKindName" <:=> pKind <** id_lit

pSpec :: Parser CBSSpec
pSpec = "SPEC"
  <::=> keyword "Auxiliary" **> pSpec
  <||>  pFuncon
  <||>  pSyntaxSpec
  <||>  pSemanticsSpec
  <||>  RuleSpec <$$> pRuleSpec
  <||>  AliasSpec <$$ keyword "Alias" <**> id_lit <** keychar '=' <**> id_lit
  <||>  OtherwiseSpec <$$ keyword "Otherwise" <**> pRule
  <||>  TypeSpec <$$ keyword "Type" <**> id_lit <**> optional pParams <**> multiple pBounded <**> optional pDefRewrite
  <||>  DatatypeSpec <$$ keyword "Datatype" <**> id_lit <**> optional pParams <**>
          optional pBounded <**> optionalWithDef (keyword "::=" **> pDataAlts) []
  <||>  EntitySpec <$$ keyword "Entity" <**> pEntityDecl
  <||>  MetaVariablesSpec . concat <$$ keyword "Meta-variables" <**> (many1 pVarDecl)

pVarDecl :: Parser [VarDecl]
pVarDecl = "VARS-DECL"
  <:=> apply <$$> manySepBy1 alt_id_lit (keychar ',') <**>
          (Left <$$ keyword "<:" <**> pTerm  <||>
           Right <$$ keychar ':' <**> pTerm)
  where apply vars (Left ty)  = map (flip VarDeclSubType ty) vars
        apply vars (Right ty) = map (flip VarDeclType ty) vars

pFuncon :: Parser CBSSpec
pFuncon = "FUNCON"
  <::=> build_funcon <$$ keyword "Funcon" <**> id_lit
                     <**> optional pParams
                     <**  keychar ':'
                     <**> pTerm
                     <**> optional pDefRewrite
  where build_funcon nm mparams cs = FunconSpec nm mparams cs

pSemanticsSpec :: Parser CBSSpec
pSemanticsSpec = "SEMANTICS"
  <:=> SemanticsSpec <$$ keyword "Semantics" <**> name_lit <** keyword "[[" <**>
        pVar <** keychar ':' <**> pPhraseType <** keyword "]]" <**>
        optional pParams <** keychar ':' <**> pTerm <**> optional pDefEqual

-- ambiguity "(X:T,Y:T)
-- alternative interpretation:
pParams :: Parser Params
pParams = "PARAMS"
  <::=> keychar '(' **> multipleSepBy pParam (keychar ',') <** keychar ')'

pParam :: Parser Param
pParam = "PARAM"
  <::= Param <$$> pVar <**> optional pBounded

pDefEqual :: Parser DefEqual
pDefEqual = "DEFINED-EQUAL" <::=> DefEqual <$$ keychar '=' <**> pTerm
pDefRewrite :: Parser DefRewrite
pDefRewrite = "DEFINED-REWRITE" <::=> DefRewrite <$$ keyword "~>" <**> pTerm

pBounded :: Parser Bounds
pBounded = "BOUNDED"
  <:=> InType <$$ keychar ':' <**> pType
  <||> Sub    <$$ keyword ">:" <**> pType
  <||> Sup    <$$ keyword "<:" <**> pType

pDataAlts :: Parser [DatatypeAlt]
pDataAlts = "ALT+ |" <:=> multipleSepBy pDataAlt (keychar '|')

pDataAlt :: Parser DatatypeAlt
pDataAlt = "ALT"
  <:=> AltDots <$$ keyword "..."
  <||> Inj <$$ keychar '{' <**> pVar <** keychar ':' <**> pType <** keychar '}'
  <||> Cons <$$> id_lit <**> optional pParams

pEntityDecl :: Parser Entity
pEntityDecl = "ENTITY"
  <:=> EntContextual <$$> pEnt <** keyword "|-" <** keychar '_' <**> pArrow
                                                <** keychar '_'
  <||> EntMutable <$$>  angles ((keychar '_' **> keychar ',') **> pEnt) <**>
                        pArrow <**>
                        angles ((keychar '_' **> keychar ',') **> pEnt)
  <||> EntObservable <$$ keychar '_' <**> pEntArrow <** keychar '_'

pEnt :: Parser Ent
pEnt = "ENT"
  <:=> EntVarStem <$$> pVarStem <**> optional (pPolarity)
  <||> EntName <$$> name_lit <**> optional pPolarity <**
          keychar '(' <**> pVar <** keychar ':' <**> pTerm <** keychar ')'

pEntArrow :: Parser EntArrow
pEntArrow = "ENT-ARROW"
  <:=> EADynamic <$$ keyword "--" <**> pEnt <** keyword "->"
  <||> EAStatic <$$ keyword "==" <**> pEnt <** keyword "=>"

pComment :: Parser CBSSpec
pComment = "COMMENT"
  <:=> CommentSpec <$$ keyword "/*" <**> multiple pCommentPart <** keyword "*/"
  <||> MetaSpec . HS_Imports <$$ keyword "/*HS-IMPORTS"
                    <**> token "ORDINARY" <** keyword "*/"

pCommentPart :: Parser CommentPart
pCommentPart = "COMMENT-PART"
  <::=> Ordinary    <$$> token "ORDINARY"
  <||>  Asterisk    <$$ keychar '*'
  <||>  At          <$$ keychar '@' <**> optionalWithDef (token "SECT-NUM") ""
  <||>  At          <$$> token "SECT-NUM"
  <||>  CommentTerm <$$ token "TICK" <**> multipleSepBy1 pTerm (keychar ',') <** token "TICK"
  <||>  CommentPremise <$$ token "TICK" <** token "TICK" <**> pPremise
                            <** token "TICK" <** token "TICK"
  <||>  SpecInComment <$$ token "TICK" <** token "TICK" <** token "TICK"
                          <**> pSpec
                      <** token "TICK" <** token "TICK" <** token "TICK"

-- sections
pKind :: Parser String
pKind = "KIND" <:=>
  keyword "Funcon" <||> keyword "Type" <||> keyword "Datatype" <||>
  keyword "Entity" <||> keyword "Lexis" <||> keyword "Syntax" <||>
  keyword "Semantics" <||> keyword "Alias"

-- related to syntax
pSyntaxSpec :: Parser CBSSpec
pSyntaxSpec = "SYNTAX-SPEC"
  <:=> SyntaxSpec <$$ keyword "Syntax" <**> multiple1 pProd
  <||> LexisSpec <$$ keyword "Lexis" <**> multiple1 pProd

pProd :: Parser Prod
pProd = "PROD"
  <:=> Prod <$$> optionalWithDef (pVarStems) [] <**> pSynName <**
                  keyword "::=" <**> pAlts
  <||> SDFComment [] <$$ keyword "SDF" <** pComment


