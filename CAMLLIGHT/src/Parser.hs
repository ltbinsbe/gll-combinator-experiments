
module Parser where

import Shared
import Concrete

-- import GLL.Combinators.Interface hiding (Assoc(..), Fixity(..))
-- import GLL.Combinators.BinaryInterface hiding (Assoc(..), Fixity(..))
import GLL.ParserCombinators hiding (Assoc(..), Fixity(..))
-- import GLL.ParserCombinatorsLookahead hiding (Assoc(..), Fixity(..))

import qualified Data.IntMap as IM

-- #2.2
pGlobalName :: BNF Token GlobalName
pGlobalName = "global-name"
  <:=>  Unqual  <$$> id_lit
  <||>  Qal     <$$> id_lit <** keyword "__" <**> id_lit

-- DEVIATION #3
pCapGlobalName :: BNF Token GlobalName
pCapGlobalName = "cap-global-name"
  <:=>  Unqual  <$$> alt_id_lit
  <||>  Qal     <$$> id_lit <** keyword "__" <**> alt_id_lit

pVar :: BNF Token Var
pVar = "variable"
  <:=> Var <$$> pGlobalName
  <||> Prefix <$$ keyword "prefix" <**> pOpName
 where
    pOpName :: BNF Token Op
    pOpName = chooses "operator-name" (map keyword operator_names)

pCConstr :: BNF Token CConstr
pCConstr = "cconstr"
  <:=> CCons  <$$> pCapGlobalName{- DEVIATION #3 -}
  <||> Nil    <$$ keychar '[' <** keychar ']'
  <||> NilVec <$$ keyword "[|" <** keyword "|]" {- DEVIATION #4 -}
  <||> Void   <$$ keychar '(' <** keychar ')'
  <||> CTrue  <$$ keyword "true" -- DEVIATION #3
  <||> CFalse <$$ keyword "false" -- DEVIATION #3

pNConstr :: BNF Token NCConstr
pNConstr = "ncconstr"
  <:=> NCCons <$$> pCapGlobalName{- DEVIATION #3 -}
  <||> Cons   <$$ keyword "prefix" <** keyword "::"

pTyCons :: BNF Token TyCons
pTyCons = "typeconstr" <:=> TyConsWrap <$$> pGlobalName

pLabel :: BNF Token Label
pLabel = "label" <:=> LabelWrap <$$> pGlobalName

-- #2.4
pTyExpr :: BNF Token TyExpr
pTyExpr = "typexpr"
  <::= {- DISAMBIGUATION -}
        TyArrow       <$$> pTyExpr <** keyword "->" <<<**> {-DISAMBIG-} pTyExpr
  <||>  shortest_match ({-DISAMBIGUATION-}
           TyProd     <$$> ((:) <$$> pTyExpr <**>
                                      multiple1 (keyword "*" **> pTyExpr)) )
  <||>  TyCons        <$$> pTyCons
  <||>  TyApp . (:[]) <$$> pTyExpr <**> pTyCons
  <||>  TyApp         <$$>
               parens ((:) <$$> pTyExpr <**> multiple1 (keyword "," **> pTyExpr))
          <**> pTyCons
  <||>  TyIdent       <$$  keyword "'" <**> id_lit
  <||>                     parens pTyExpr

-- #2.5
pConstant :: BNF Token Constant
pConstant = "constant"
  <:=> CIntLit      <$$> int_lit
  <||> CStringLit   <$$> string_lit
  <||> CFloatLit    <$$> float_lit
  <||> CCharLit     <$$> token "CHAR"
  <||> CConstr      <$$> pCConstr

-- #2.6
pPattern :: BNF Token Pattern
pPattern = "pattern"
  <::=  PatAs     <$$> pPattern <** keyword "as" <**> id_lit
  <||>  PatAlt    <$$> pPattern <** keyword "|" <**>>> {-DISAMBIGUATION-} pPattern
  <||>  shortest_match (
          patProd <$$> pPattern <** keyword "," <**> pPattern <**>
                          multiple (keyword "," **> pPattern) )
  <||>  PatCons   <$$> pPattern <** keyword "::" <<<**> {-DISAMBIGUATION-} pPattern
  <||>  PatCApp   <$$> pNConstr <**> pPattern
  <||>   (PatAny    <$$  keyword "_"
  <||>  PatIdent  <$$> id_lit
  <||>                 parens pPattern
  <||>                 parens (PatTy <$$> pPattern <** keyword ":" <**> pTyExpr)
    -- left associative
  <||>  PatConst  <$$> pConstant
  <||>  PatRec    <$$> braces (multipleSepBy1 pPatEntry (keyword ";"))
  --  <||>  PatNil    <$$  keychar '[' <** keychar ']' -- DEVIATION #7
  <||>  PatList   <$$> brackets (multipleSepBy1 pPattern (keyword ";")) )
  <||>  PatRange  <$$> token "CHAR" <** keyword ".." <**> token "CHAR" {- EXTENSION -}
  where patProd :: Pattern -> Pattern -> [Pattern] -> Pattern
        patProd p1 p2 ps = PatProd $ p1 : (p2 : ps)

        pPatEntry :: BNF Token PatEntry
        pPatEntry = "pat-entry"
          <:=> PatEntry <$$> pLabel <** keyword "=" <**> pPattern

-- #2.7
pPatternList :: BNF Token Patterns
pPatternList = "pattern-list" <:=> multiple1 pPattern

-- IMPORTANT, mutually recursive with pExpr
pSMatching :: BNF Token SMatchings
pSMatching = "simple-matching"
  <:=>  longest_match ( {- DISAMBIGUATION -}
          optional (keyword "|") {- DEVIATION #8 -} **>
          someSepBy1 (SMatching <$$> pPattern <**> optional pGuard <** keyword "->" <**>
                      pExpr) (keyword "|") )

-- IMPORTANT, mutually recursive with pExpr
pMatchings :: BNF Token Matchings
pMatchings = "multiple-matching"
  <:=>  longest_match ({- DISAMBIGUATION -}
          optional (keyword "|") {- DEVIATION #8 -} **>
          someSepBy1 (Matching <$$> pPatternList <**> optional pGuard <** keyword "->" <**>
                      pExpr) (keyword "|") )

pGuard :: BNF Token Expr
pGuard = "guard" <:=> keyword "when" **> pExpr

pLetBindings :: BNF Token LetBindings
pLetBindings = "let-bindings" <:=> multipleSepBy1 pLetBinding (keyword "and")

pLetBinding :: BNF Token LetBinding
pLetBinding = "let-binding"
  <:=> LetConst <$$> pPattern <** keyword "=" <**> pExpr
  <||> LetAbs   <$$> pVar <**> pPatternList <** keyword "=" <**> pExpr

pPrefixOp :: BNF Token Op
pPrefixOp = chooses "prefix-op" [ keyword op | op <- prefix_ops ]

pInfixOp :: BNF Token Op
pInfixOp = chooses "infix-op" [ keyword op | op <- infix_ops ]

pExpr :: BNF Token Expr
pExpr = "expr-0"
  <::= {- ExIdent <$$> id_lit
  <||>  DEVIATION #5 -}
      ( ExMatch <$$  keyword "match" <**> pExpr <** keyword "with" <**> pSMatching
  <||>  ExWhere <$$> pExpr <** keyword "where" <**> (maybe False (const True) <$$> optional (keyword "rec")) <**> pLetBinding
  <||>  pLetComponent "-in" ExLet <** keyword "in" <**> pExpr
  <||>  ExFun   <$$  keyword "fun" <**> pMatchings
  <||>  ExFunc  <$$  keyword "function" <**> pSMatching
  <||>  ExTry   <$$  keyword "try" <**> pExpr <** keyword "with" <**> pSMatching
      )
  <||>  ExSeq   <$$> pExpr <** keyword ";" <<<**> pExpr
  <||>  ExITE   <$$  keyword "if" <**> pExpr <** keyword "then" <**> pExpr
                <**>>> {- DISAMBIGUATION -} optional (keyword "else" **> pExpr)
  <||>( exAcc   <$$> pExpr <**> pLabExpr <<<**> optional (keyword "<-" **> pExpr)
  <||>  ExCMut  <$$> pExpr <<<** keyword "<-" **> pExpr
  <||>  exAss   <$$> pExpr <** keyword ":=" <<<**> pExpr
      )
  <||>  shortest_match ( (ExProd .) . (:)
                <$$> pExpr <** keyword "," <**> multipleSepBy1 pExpr (keyword ",") )
  <||>  ExOr    <$$> pExpr <** keyword "or" <**>>> pExpr
  <||>  ExOr    <$$> pExpr <** keyword "||" <**>>> pExpr
  <||>  ExAnd   <$$> pExpr <** keyword "&" <**>>> pExpr
  <||>  ExAnd   <$$> pExpr <** keyword "&&" <**>>> pExpr
  <||>  pExOperators3 (
  "expr-end" <::=
  ExCApp  <$$> pNConstr <**> pExpr
  <||>  ExApp   <$$> pExpr <**>>> pExpr -- DISAMBIGUATION
  <||>  ExPrefix <$$> keyword "!" <**> pExpr
  <||>( ExVar   <$$> pVar
  <||>  shortest_match (
          ExList  <$$> brackets (multipleSepBy1 pExpr (keyword ";")) )
  <||>  shortest_match (
          ExVec   <$$> within (keyword "[|") (multipleSepBy1 pExpr (keyword ";"))
                            (keyword "|]") )
  <||>  shortest_match (
          ExRec   <$$> braces (multipleSepBy1 pEntry (keyword ";")) )
  <||>  ExConst <$$> pConstant
  <||>               parens pExpr
  <||>               within (keyword "begin") pExpr (keyword "end")
  <||>               parens (ExTy <$$> pExpr <** keyword ":" <**> pTyExpr)
  <||>  ExWhile <$$  keyword "while" <**> pExpr <** keyword "do" <**> pExpr <**
                      keyword "done"
  <||>  ExFor   <$$  keyword "for" <**> id_lit <** keyword "=" <**> pExpr <**>
                      pDir <**> pExpr <** keyword "do" <**> pExpr <** keyword "done"
      ) )
  where pEntry :: BNF Token Entry
        pEntry = "entry" <:=> Entry <$$> pLabel <** keyword "=" <**> pExpr

        pLabExpr :: BNF Token MutType
        pLabExpr =  "lab-expr"
          <:=> Record <$$  keyword "."  <**> pLabel
          <||> Vector <$$  keyword ".(" <**> pExpr <** keychar ')'
          <||> String <$$  keyword ".[" <**> pExpr <** keychar ']'

        pDir :: BNF Token Dir
        pDir = "dir" <:=> To <$$ keyword "to" <||> DownTo <$$ keyword "downto"

        exAcc :: Expr -> MutType -> Maybe Expr -> Expr
        exAcc expr (Vector expr2) Nothing = ExVAcc expr expr2
        exAcc expr (String expr2) Nothing = ExSAcc expr expr2
        exAcc expr (Record lab) Nothing = ExRAcc expr lab
        exAcc expr (Vector expr2) (Just expr3) = ExVMut expr expr2 expr3
        exAcc expr (String expr2) (Just expr3) = ExSMut expr expr2 expr3
        exAcc expr (Record lab) (Just expr2) = ExRMut expr lab expr2

        exAss e1 e2 = ExInfix e1 ":=" e2

data MutType = Vector Expr | Record Label | String Expr

pExOperators0 :: BNF Token Expr -> BNF Token Expr
pExOperators0 rest = "op-expr"
  <:=> ExPrefix <$$> pPrefix <**> pExpr
  <||> ExInfix <$$> pExpr <**> pInfix <**> pExpr
  <||> rest
  where pPrefix = chooses "prefix-operator"
                    [ keyword op | row <- ops_priorities, (op, PreFix, _) <- row ]
        pInfix = chooses "infix-operator"
                    [ keyword op | row <- ops_priorities, (op, InFix, _) <- row ]


pExOperators1 :: BNF Token Expr -> BNF Token Expr
pExOperators1 rest = doLevel table
  where table = zip [1..] (reverse ops_priorities)
        doLevel :: [(Int, [(String, Fixity, Assoc)])] -> BNF Token Expr
        doLevel arg@[(ix,last)] =
          chooses (ntName ix) (choices (doLevel arg) rest last ++ [id <$$> rest])
        doLevel arg@((ix,row):others) =
          chooses (ntName ix) (choices (doLevel arg) cont row ++ [id <$$> cont])
          where cont = doLevel others

--        choices :: BNF Token Expr -> BNF Token Expr -> [(String, Fixity, Assoc)]
--                      -> [AltExpr Token Expr]
        choices curr next = map symb
          where --symb :: (String, Fixity, Assoc) -> AltExpr Token Expr
                symb (op, fix, assoc) = case fix of
                  PreFix -> ExPrefix <$$> keyword op <**> curr
                  InFix -> case assoc of
                    LAssoc  -> ExInfix <$$> curr <**> keyword op <**> next
                    RAssoc  -> ExInfix <$$> next <**> keyword op <**> curr
                    _       -> ExInfix <$$> curr <**> keyword op <**> curr

        ntName i = show i ++ "-op-row"

pExOperators2 :: BNF Token Expr -> BNF Token Expr
pExOperators2 rest = table IM.! 1
  where table = IM.mapWithKey mkNterm $ IM.fromList $
                  zip [1..] (reverse ops_priorities)
        max_ix = length ops_priorities

        mkNterm ix ops = chooses (ntName ix) $
          ( [ mkAlt op fix assoc | (op, fix, assoc) <- ops ] ++ [id <$$> next] )
          where mkAlt op fix assoc = case fix of
                  PreFix  -> ExPrefix <$$> keyword op <**> curr
                  InFix   -> case assoc of
                    LAssoc -> ExInfix <$$> curr <**> keyword op <**> next
                    RAssoc -> ExInfix <$$> next <**> keyword op <**> curr
                    _      -> ExInfix <$$> curr <**> keyword op <**> curr

                next | ix == max_ix = rest
                     | otherwise    = table IM.! (ix + 1)
                curr                = table IM.! ix

        ntName i = show i ++ "-op-row"

pExOperators3 :: BNF Token Expr -> BNF Token Expr
pExOperators3 rest = chooses_prec "op-exprs" $
  [ mkNterm ix row
  | (ix, row) <- zip [1..] (reverse ops_priorities)
  ] ++ [rest]

  where mkNterm ix ops = chooses (ntName ix) $
          [ mkAlt op fix assoc | (op, fix, assoc) <- ops ]
          where mkAlt op fix assoc = case fix of
                  PreFix  -> ExPrefix <$$> keyword op <**> pExpr
                  InFix   -> case assoc of
                    LAssoc -> ExInfix <$$> pExpr <**> keyword op <**>>> pExpr
                    RAssoc -> ExInfix <$$> pExpr <**> keyword op <<<**> pExpr
                    _      -> ExInfix <$$> pExpr <**> keyword op <**> pExpr

        ntName i = show i ++ "-op-row"



pLetComponent :: String -> (Bool -> LetBindings -> a) -> BNF Token a
pLetComponent c cons = "let-component" ++ c
  <:=> cons <$$ keyword "let" <**>
    (maybe False (const True) <$$> optional (keyword "rec")) <**> pLetBindings

-- #2.8
pTypeDefinition :: BNF Token TyDefs
pTypeDefinition = "type-definition"
  <:=> keyword "type" **> multipleSepBy1 pTyDef (keyword "and")

pTyDef :: BNF Token TyDef
pTyDef = "typedef"
  <:=> VariantTy  <$$> pTyParams <**> id_lit <** keyword "=" <**> pConstDecls
  <||> RecordTy   <$$> pTyParams <**> id_lit <** keyword "=" <**> pLabelDecls
  <||> TySynonym  <$$> pTyParams <**> id_lit <** keyword "==" <**> pTyExpr
  <||> AbstractTy <$$> pTyParams <**> id_lit

pTyParams :: BNF Token TyParams
pTyParams = "type-params"
  <:=> satisfy []
  <||> (:[]) <$$ keyword "'" <**> id_lit
  <||> parens (multipleSepBy1 (keyword "'" **> id_lit) (keyword ","))

pConstDecls :: BNF Token ConstDecls
pConstDecls = "const-decls" <:=> multipleSepBy1 pConstDecl (keyword "|")

pConstDecl :: BNF Token ConstDecl
pConstDecl = "const-decl"
  <:=> CConstDecl <$$> alt_id_lit {- DEVIATION #3 -}
  <||> NCConstDecl <$$> alt_id_lit {- DEVIATION #3 -} <** keyword "of" <**> (maybe False (const True) <$$> (optional (keyword "mutable"))) <**> pTyExpr

pLabelDecls :: BNF Token LabelDecls
pLabelDecls = "label-decls" <:=> braces (multipleSepBy1 pLabelDecl (keyword ";"))

pLabelDecl :: BNF Token LabelDecl
pLabelDecl = "label-decl"
  <:=> LabelDecl <$$>
        (maybe False (const True) <$$> optional (keyword "mutable")) <**>
        id_lit <** keyword ":" <**> pTyExpr

pExcDefinition :: BNF Token ExcDef
pExcDefinition = "exception-definition"
  <:=> keyword "exception" **> multipleSepBy1 pConstDecl (keyword "and")
-- #2.9

pDirective :: BNF Token Directive
pDirective = "directive" <:=> bDir <$$ keyword "#" <**> id_lit <**> string_lit
  where bDir "open"   = DirOpen
        bDir "close"  = DirClose
        bDir id       = DirOther id

-- #2.10

pModule :: BNF Token Module
pModule = "module" <:=> Module <$$> multiple (pPhrase <** keyword ";;")

pPhrase :: BNF Token Phrase
pPhrase = "impl-phrase"
  <:=>  Command <$$> pExpr
  <||>  pLetComponent "" ValDef
  <||>  TyDef <$$> pTypeDefinition
  <||>  ExcDef <$$> pExcDefinition
  <||>  PhrDirective <$$> pDirective

