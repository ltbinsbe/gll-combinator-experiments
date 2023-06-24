

-- UUAGC 0.9.52.1 (src/Concrete.ag)
module Concrete where

import Shared

-- CConstr -----------------------------------------------------
data CConstr = CCons (GlobalName)
             | Nil
             | NilVec
             | Void
             | CTrue
             | CFalse
             deriving ( Show)
-- ConstDecl ---------------------------------------------------
data ConstDecl = CConstDecl (Ident)
               | NCConstDecl (Ident) Bool {- EXTENSION, mutable? -} (TyExpr)
               deriving ( Show)
-- ConstDecls --------------------------------------------------
type ConstDecls = [ConstDecl]
-- Constant ----------------------------------------------------
data Constant = CIntLit Int
              | CStringLit String
              | CCharLit String 
              | CFloatLit Double 
              | CConstr (CConstr)
              deriving ( Show)
-- Dir ---------------------------------------------------------
data Dir = To
         | DownTo
         deriving ( Enum,Show)
-- Entries -----------------------------------------------------
type Entries = [Entry]
-- Entry -------------------------------------------------------
data Entry = Entry (Label) (Expr)
           deriving ( Show)
-- ExcDef ------------------------------------------------------
type ExcDef = [ConstDecl]
-- Expr --------------------------------------------------------
data Expr = ExVar (Var)
          | ExConst (Constant)
          | ExTy (Expr) (TyExpr)
          | ExProd (Exprs)
          | ExCApp (NCConstr) (Expr)
          | ExList (Exprs)
          | ExVec (Exprs)
          | ExRec (Entries)
          | ExApp (Expr) (Expr)
          | ExPrefix (Op) (Expr)
          | ExInfix (Expr) (Op) (Expr)
          | ExVAcc (Expr) (Expr)
          | ExRAcc (Expr) (Label)
          | ExSAcc (Expr) (Expr)
          | ExVMut (Expr) (Expr) (Expr)
          | ExRMut (Expr) (Label) (Expr)
          | ExSMut (Expr) (Expr) (Expr)
          | ExCMut (Expr) (Expr)
          | ExAnd (Expr) (Expr)
          | ExOr (Expr) (Expr)
          | ExITE (Expr) (Expr) (OptExpr)
          | ExWhile (Expr) (Expr)
          | ExFor (Ident) (Expr) (Dir) (Expr) (Expr)
          | ExSeq (Expr) (Expr)
          | ExMatch (Expr) (SMatchings)
          | ExFun (Matchings)
          | ExFunc (SMatchings)
          | ExTry (Expr) (SMatchings)
          | ExLet (Bool) (LetBindings) (Expr)
          | ExWhere Expr Bool {- recursive? -} LetBinding  -- EXTENSION
          deriving ( Show)
-- Exprs -------------------------------------------------------
type Exprs = [Expr]
-- GlobalName --------------------------------------------------
data GlobalName = Unqual (Ident)
                | Qal (Ident) (Ident)
                deriving ( Show)
-- Label -------------------------------------------------------
data Label = LabelWrap (GlobalName)
           deriving ( Show)
-- LabelDecl ---------------------------------------------------
data LabelDecl = LabelDecl (Bool) (Ident) (TyExpr)
               deriving ( Show)
-- LabelDecls --------------------------------------------------
type LabelDecls = [LabelDecl]
-- LetBinding --------------------------------------------------
data LetBinding = LetConst (Pattern) (Expr)
                | LetAbs (Var) (Patterns) (Expr)
                deriving ( Show)
-- LetBindings -------------------------------------------------
type LetBindings = [LetBinding]
-- Matching ----------------------------------------------------
data Matching = Matching (Patterns) (Maybe Expr) {- EXTENSION guard -} (Expr)
              deriving ( Show)
-- Matchings ---------------------------------------------------
type Matchings = [Matching]
-- Module ------------------------------------------------------
data Module = Module (Phrases)
            deriving ( Show)
-- NCConstr ----------------------------------------------------
data NCConstr = NCCons (GlobalName)
              | Cons
              deriving ( Show)
-- OptExpr -----------------------------------------------------
type OptExpr = Maybe (Expr)
-- PatEntries --------------------------------------------------
type PatEntries = [PatEntry]
-- PatEntry ----------------------------------------------------
data PatEntry = PatEntry (Label) (Pattern)
              deriving ( Show)
-- Pattern -----------------------------------------------------
data Pattern = PatIdent (Ident)
             | PatAny
             | PatAs (Pattern) (Ident)
             | PatTy (Pattern) (TyExpr)
             | PatAlt (Pattern) (Pattern)
             | PatConst (Constant)
             | PatCApp (NCConstr) (Pattern)
             | PatProd (Patterns)
             | PatRec (PatEntries)
             | PatList (Patterns)
             | PatCons (Pattern) (Pattern)
             | PatRange String String  {- EXTENSION -}
             deriving ( Show)
-- Patterns ----------------------------------------------------
type Patterns = [Pattern]
-- Phrase ------------------------------------------------------
data Phrase = Command (Expr)
            | ValDef (Bool) (LetBindings)
            | TyDef (TyDefs)
            | ExcDef (ExcDef)
            | PhrDirective Directive
            deriving ( Show)
-- Phrases -----------------------------------------------------
type Phrases = [Phrase]
-- SMatching ---------------------------------------------------
data SMatching = SMatching (Pattern) (Maybe Expr) {- EXTENSION guard -} (Expr)
               deriving ( Show)
-- SMatchings --------------------------------------------------
type SMatchings = [SMatching]
-- TyCons ------------------------------------------------------
data TyCons = TyConsWrap (GlobalName)
            deriving ( Show)
-- TyDef -------------------------------------------------------
data TyDef = VariantTy (TyParams) (Ident) (ConstDecls)
           | RecordTy (TyParams) (Ident) (LabelDecls)
           | TySynonym (TyParams) (Ident) (TyExpr)
           | AbstractTy (TyParams) (Ident)
           deriving ( Show)
-- TyDefs ------------------------------------------------------
type TyDefs = [TyDef]
-- TyExpr ------------------------------------------------------
data TyExpr = TyIdent (Ident)
            | TyArrow (TyExpr) (TyExpr)
            | TyProd (TyExprs)
            | TyApp (TyExprs) (TyCons)
            | TyCons (TyCons)
            deriving ( Show)
-- TyExprs -----------------------------------------------------
type TyExprs = [TyExpr]
-- TyParams ----------------------------------------------------
type TyParams = [(Ident)]
-- Var ---------------------------------------------------------
data Var = Var (GlobalName)
         | Prefix (Op)
         deriving ( Show)

data Directive = DirOpen String
               | DirClose String
               | DirOther Ident String
               deriving Show
