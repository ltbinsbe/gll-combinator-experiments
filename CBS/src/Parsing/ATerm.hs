{-# LANGUAGE FlexibleInstances, StandaloneDeriving, TupleSections #-}

module Parsing.ATerm where

import Types.SourceAbstractSyntax

import CCO.Tree
import CCO.Feedback
import CCO.Printing
import CCO.Component

import Control.Monad
import Data.List (intercalate)
import Data.Char (isDigit)
import Data.Either (rights)
import Data.Maybe (catMaybes)

-- arguments indicates whether unspecified funcons should be generated
aterm2cbs :: Bool -> Component ATerm CBSFile
aterm2cbs = component . pCBSFile

type Parser a = ATerm -> Feedback a
type Builder a = [ATerm] -> Feedback a

pCBSFile :: Bool -> Parser CBSFile
pCBSFile pholder aterm = CBSFile <$> pFSpecs pholder aterm

data DocPart = EntityDef ATerm
            | TypeSyn String ATerm ATerm
            | TypeDef String ATerm [ATerm]
            | FunconSpecRep (Maybe [ATerm]) [ATerm] [[ATerm]] -- comment:signature:rules

-- A cbs file is represented by [ATerm]
-- This function divides the [ATerms] according to what they specify
-- (entity, datatype, typesynonym or funcon; other specs are ignored)
-- first argument specifies whether a placeholder funcon should be inserted
-- for unspecified funcons
divSpecs :: Bool -> [ATerm] -> Maybe [ATerm] -> Maybe [ATerm] -> [[ATerm]] -> [DocPart]
divSpecs ph [] mdoc msig rules = newFSpec mdoc msig rules
-- unspecified type synonym
divSpecs ph ((App "Type" [String nm, mparams
         ,App "Some" [App "Type" [App "TypeDots" _]]]):rest)
         mdoc msig rules = newFSpec mdoc msig rules ++ divSpecs ph rest Nothing Nothing []
-- type synonym
divSpecs ph (spec@(App "Type" [String nm, mparams, App "Some" [App "Type" [mty]]]):rest)
        mdoc msig rules = TypeSyn nm mparams mty : newFSpec mdoc msig rules ++
                            divSpecs ph rest Nothing Nothing []
-- datatype
divSpecs ph (spec@(App "Datatype" [String nm, mparams, List malts]):rest)
        mdoc msig rules = TypeDef nm mparams malts : newFSpec mdoc msig rules ++
                            divSpecs ph rest Nothing Nothing []
-- entity
divSpecs ph (spec@(App "Entity" [rel]):rest)
        mdoc msig rules = EntityDef rel : newFSpec mdoc msig rules ++
                            divSpecs ph rest Nothing Nothing []

-- unspecified funcon
divSpecs ph ((App "Funcon" sig@[_,_,App "TypeValue" [_,App "TermDots" _]]):rest)
        mdoc msig rules = newFSpec mdoc msig rules ++ fspec ++ divSpecs ph rest Nothing Nothing []
  where fspec | ph        = [FunconSpecRep Nothing sig []]
              | otherwise = []
-- unspecified funcon with comment in front of it
divSpecs ph ((App "Comment" cs):(App "Funcon" sig@[_,_,App "TypeValue" [_,App "TermDots" _]]):rest)
        mdoc msig rules = newFSpec mdoc msig rules ++ fspec ++ divSpecs ph rest Nothing Nothing []
  where fspec | ph        = [FunconSpecRep (Just cs) sig []]
              | otherwise = []
-- look 'inside' Auxiliary
divSpecs ph ((App "Auxiliary" [spec]):rest)
        mdoc msig rules = newFSpec mdoc msig rules ++
                            divSpecs ph (spec:rest) Nothing Nothing []
-- funcon sig with comment in front of it
divSpecs ph ((App "Comment" [List cs]):(App "Funcon" sig):rest)
        mdoc msig rules = newFSpec mdoc msig rules ++ divSpecs ph rest (Just cs) (Just sig) []
-- funcon sig without comment in front of it
divSpecs ph ((App "Funcon" sig):rest)
        mdoc msig rules = newFSpec mdoc msig rules ++ divSpecs ph rest Nothing (Just sig) []

-- ignore otherwise rules (we do not generate translation equations)
-- Edited by Neil, 10/04/16
divSpecs ph ((App "Otherwise" rule):rest)
        mdoc msig rules = newFSpec mdoc msig rules ++ divSpecs ph rest Nothing Nothing []
-- ignore rules for translation equations
-- divSpecs ph ((App "Rule" [App "Axiom" [App "Equation" [App "SemanticsApp" _,_]]]):rest)
divSpecs ph ((App "Rule" [App "Axiom" [App "Equation" (App "SemanticsApp" _ : _)]]):rest)
        mdoc msig rules = newFSpec mdoc msig rules ++ divSpecs ph rest Nothing Nothing []
-- divSpecs ph ((App "Rule" [App "Axiom" [App "Axiom" [App "Equation" -- why nested Axioms?
--            [App "SemanticsAppTerm" _,_]]]]):rest)
divSpecs ph ((App "Rule" [App "Axiom" [App "Equation"
            (App "SemanticsAppTerm" _ : _)]]):rest)
        mdoc msig rules = newFSpec mdoc msig rules ++ divSpecs ph rest Nothing Nothing []
-- funcon rule
divSpecs ph ((App "Rule" rule):rest) mdoc msig@(Just _) rules =
        divSpecs ph rest mdoc msig (rules++[rule])
divSpecs pholder (_:rest) mdoc msig rules =
        newFSpec mdoc msig rules ++ divSpecs pholder rest Nothing Nothing []

-- maybe creates a new funconspec based on the arguments
newFSpec :: Maybe [ATerm] -> Maybe [ATerm] -> [[ATerm]] -> [DocPart]
newFSpec mdoc (Just sig) rules  = [FunconSpecRep mdoc sig rules]
newFSpec _ _ _                  = []

-- Turn a grouped document (represented by [DocPart]) into a [CBSSpec]
parseDocParts :: [DocPart] -> Feedback [CBSSpec]
parseDocParts = mapM parseDocPart

-- Attempts to parse each document partition into a CBS specification
parseDocPart :: DocPart -> Feedback CBSSpec
parseDocPart (FunconSpecRep mdoc sig rules) = funconSpec mdoc sig rules
parseDocPart (TypeSyn nm mparams mty) = do
    params <- pSigParams mparams
    ty <- pTerm mty
    return (TypeSynonymSpec (TypeSynonymDecl nm params ty))
parseDocPart (EntityDef rel) = do
    fspec <- case rel of
        -- mutable entity, in the left state we find its name and default val
        App "Effect" [_,App "State" [_,List [App "Mutable" [String lnm,def]]], _,
            App "State" [_,List [App "Mutable" [String rnm,pat]]]] -> do
           MutableSpec <$>  ((\(a,b) -> (lnm,a,b)) <$> pTypedTerm def) <*>
                            ((\(a,b) -> (rnm,a,b)) <$> pTypedPatt pat)
        -- inherited entity, inside the context
        App "Eval" [App "Some" [App "Context"
                [List [App "Inherited" [String nm,term]]]], _, _, _] -> do
            InheritedSpec <$> ((\(a,b) -> (nm,a,b)) <$> pTypedTerm term)
        -- control/input/output entities
        App "Eval" [App "None" _,_,App "NormalEmitted" [List [emit]],_] ->
            case emit of
                App "Emitted" [String nm, App"Some"[String "!"], pat] ->
                    OutputSpec <$> ((\(a,b)->(nm,a,b)) <$> pTypedPatt pat)
                App "Emitted" [String nm, App"Some"[String "?"], pat] ->
                    InputSpec <$> ((\(a,b)->(nm,a,b)) <$> pTypedPatt pat)
                App "Emitted" [String nm, App "None" _, ty] ->
                    ControlSpec <$> ((nm,) . snd <$> pTypedPatt ty)
    return (EntitySpec fspec)
parseDocPart (TypeDef nm mparams malts) = do
    params <- pSigParams mparams
    alts <- pDataTypeAlts nm malts
    return (DataTypeSpec (DataTypeDecl nm params alts))


pFSpecs :: Bool -> Parser [CBSSpec]
pFSpecs pholder start  = case start of
    (App "LanguagePart" [_, List specs, sects])  ->
        parseDocParts $ divSpecs pholder (specs ++ sectionSpecs sects) Nothing Nothing []
    (App "Part" [List specs, sects])    ->
        parseDocParts $ divSpecs pholder (specs ++ sectionSpecs sects) Nothing Nothing []
 where
        sectionSpecs :: ATerm -> [ATerm]
        sectionSpecs (App "None" _) = []
        -- Sections<x>s, x \in 1,2,3,4
        sectionSpecs (App "Some" [App sectionXs [List sects]]) = recurseSects sects
          where -- sections 1,2,3
                recurseSects ((App mHiddenSection [hd, List specs, List sects2]):sects) =
                    specs ++ recurseSects (sects++sects2)
                -- sections 4
                recurseSects ((App mHiddenSection [hd, List specs]):sects) =
                    specs ++ recurseSects sects
                recurseSects _ = []

funconSpec :: Maybe [ATerm] -> [ATerm] -> [[ATerm]] -> Feedback CBSSpec
funconSpec mdoc mfuncon rules =
    case mfuncon of
        []  -> fError ("no funcon in part")
        funcon -> do  sig <- bFSig mdoc funcon
                      fspec <- bFSpec sig rules funcon
                      return (FunconSpec fspec)

pFSort :: Parser FSort
pFSort (App "Type" [ty]) = pFSort ty
pFSort (App "TypeValue" [ty,_]) = pFSort ty
pFSort (App "Group" [ty]) = pFSort ty
pFSort (App "Computes" [ty]) = FCompSort <$> pTerm ty
pFSort (App "ComputesFrom" [ty,ty2]) = FCompFromSort <$> pTerm ty <*> pTerm ty2
pFSort mty = FValSort <$> pTerm mty

pTypedTerm :: Parser (FTerm, FValSort)
pTypedTerm (App "Group" [tterm]) = pTypedTerm tterm
pTypedTerm (App "Typed" [term,ty]) = (,) <$> pTerm term <*> pTerm ty

pMaybeTerm :: Parser (Maybe FTerm)
pMaybeTerm (App "None" _) = return Nothing
pMaybeTerm (App "Some" [term]) = Just <$> pTerm term

pTerm :: Parser FTerm
pTerm (App "Typed" [term,ty]) = pTerm term -- ignores types of typed terms
pTerm (App "EmptyList" _) = return (TList [])
pTerm (App "EmptySet" _) = return (TSet [])
pTerm (App "List" [sequence]) = TList <$> pTerms sequence
pTerm (App "Name" [String nm]) = return (TName nm)
pTerm (App "NameApp" [String nm, term]) = TApp nm <$> pTerm term
pTerm (App "Group" [terms]) = TTuple <$> pTerms terms
pTerm (App "EmptyGroup" _) = return (TTuple [])
pTerm (App "TermVar" [name]) = (TMetaVar . fst) <$> getMetaVar name
--pTerm (App "Sequence" [term1,term2]) = (\a b -> TTuple (a ++ [b])) <$> pTerms term1 <*> pTerm term2
pTerm (App "Computes" [to]) = TSortComputes <$> pTerm to
pTerm (App "ComputesFrom" [from,to]) = TSortComputesFrom <$> pTerm from <*> pTerm to
pTerm (App "Postfix" [ty, String op]) = TSortSeq <$> pTerm ty <*> pPostfix op
pTerm (App "Set" [terms]) = TSet <$> pTerms terms
pTerm (App "Map" [List kvs]) = TMap <$> mapM op kvs
    where op (App "Point" [key,value]) = (\a b -> TTuple [a,b]) <$> pTerm key <*> pTerm value
pTerm (App "Const" [String str])
    | null str = fError ("empty literal")
    | all isDigit str = return $ TLiteral (FLiteralNat (read str))
    | head str == '"' = return $ TLiteral (FLiteralString (read str))
    | head str == '\'' = return $ TLiteral (FLiteralAtom [read str])
    | otherwise         = fError ("unrecognised literal: " ++ str)
pTerm (App "TermDots" _) = return (TTuple [])
-- dealing with types
pTerm (App "Type" [ty]) = pTerm ty
pTerm (App "Union" [ty1, List tys]) = foldl TSortUnion <$> pTerm ty1 <*> mapM pTerm tys
pTerm term = fError ("missing case for pTerm: " ++ show term)

pTerms :: Parser [FTerm]
pTerms (App "Sequence" [term1, term2]) = (\a b -> a++[b]) <$> pTerms term1 <*> pTerm term2
pTerms term = (:[]) <$> pTerm term

pMaybePatterns :: Parser (Maybe [FPattern])
pMaybePatterns (App "EmptyGroup" _) = return Nothing
pMaybePatterns (App "Group" [aterm]) = Just <$> pPatterns aterm
pMaybePatterns pat = Just . (:[]) <$> pPattern pat

pGroupPatterns :: Parser [FPattern]
pGroupPatterns (App "Group" [pat]) = pPatterns pat
pGroupPatterns pat = pPatterns pat

pPatterns :: Parser [FPattern]
pPatterns mpatterns = case mpatterns of
    (App "Sequence" [term1, term2]) -> (\a b -> a++b) <$> pPatterns term1 <*> pPatterns term2
    term -> (:[]) <$> pPattern term

pMaybePattern :: Parser (Maybe FPattern)
pMaybePattern (App "None" _) = return Nothing
pMaybePattern (App "Some" [pat]) = Just <$> pGroupPattern pat
pMaybePattern pat = Just <$> pGroupPattern pat

pTypedPatt :: Parser (FPattern, FValSort)
pTypedPatt (App "Group" [tpat]) = pTypedPatt tpat
pTypedPatt (App "Typed" [pat,ty]) = (,) <$> pPattern pat <*> pTerm ty
pTypedPatt ty = (PAny,) <$> pTerm ty

pGroupPattern :: Parser FPattern
pGroupPattern (App "Group" [pat]) = pPattern pat
pGroupPattern pat = pPattern pat

pPattern :: Parser FPattern
pPattern (App "NameApp" [String con, args]) = PADT con <$> pGroupPatterns args
pPattern (App "Name" [String con]) = return $ PADT con []
pPattern (App "TermVar" [App "Wild" _]) = return $ PAny
pPattern (App "TermVar" [name]) = do   (var, mpostfix) <- getMetaVar name
                                       case mpostfix of
                                           Nothing -> return (PMetaVar var)
                                           Just op -> return (PSeqMetaVar var op)
pPattern (App "EmptyGroup" _) = return $ PTuple []
pPattern (App "Group" [patt]) = PTuple <$> pPatterns patt
pPattern (App "EmptyList" _) = return (PList [])
pPattern (App "List" [sequence]) = PList <$> pPatterns sequence
pPattern (App "Typed" [term,ty]) = PAnnotated <$> pPattern term <*> pValSorts ty
pPattern (App "Sequence" [pat1,pat2]) = (\a b -> PTuple (a ++ [b])) <$>
    pPatterns pat1 <*> pPattern pat2
pPattern (App "Const" [String str])
    | null str = fError ("empty literal")
    | all isDigit str = return $ PLit (FLiteralNat (read str))
    | head str == '"' = return $ PLit (FLiteralString (read str))
    | head str == '\'' = return $ PLit (FLiteralAtom [read str])
    | otherwise         = fError ("unrecognised literal")
pPattern arg = fError ("missing pattern in pPattern: "++ show arg)

pPostfix :: String -> Feedback SeqSortOp
pPostfix "+" = return PlusOp
pPostfix "*" = return StarOp
pPostfix "?" = return QuestionMarkOp
pPostfix op  = fError ("unknown postfix: " ++ op)

pSideConditions :: Builder [Either FPremiseStep FSideCondition]
pSideConditions = mapM pSideCondition

pSideCondition :: Parser (Either FPremiseStep FSideCondition)
pSideCondition (App "Equation" [lhs,rhs]) = Right <$> (SCPatternMatch <$> pTerm lhs <*> pGroupPattern rhs)
pSideCondition (App "Match" [lhs,rhs]) = Right <$> (SCPatternMatch <$> pTerm lhs <*> pGroupPattern rhs)
pSideCondition (App "Equality" [lhs,rhs]) = Right <$> (SCEquality <$> pTerm lhs <*> pTerm rhs)
pSideCondition (App "Inequality" [lhs,rhs]) = Right . SCNot <$> (SCEquality <$> pTerm lhs <*> pTerm rhs)
pSideCondition (App "Negation" [form]) = fmap SCNot <$> pSideCondition form
pSideCondition (App "Pred" [App "None" _, lhs, App "Type" [rhs]]) = Right <$> (
    SCIsInSort <$> pTerm lhs <*> pTerm rhs)
pSideCondition (App "Eval" [mcontext, lhs, line ,rhs]) =
    Left <$> premiseStep mcontext lhs [] line rhs []
pSideCondition (App "Effect" [mcontext, App "State" [lhs, List lstate], line
                ,App "State" [rhs, List rstate]]) = Left <$>
                premiseStep mcontext lhs lstate line rhs rstate
pSideCondition aterm = fError ("Missing side-condition: " ++ show aterm)

evalStep :: ATerm -> ATerm -> [ATerm] -> ATerm -> ATerm -> [ATerm] -> Feedback FStep
evalStep mctxt lhs lstate mline rhs rstate = do
    (signals, ins, out) <- femitted
    FStep <$> fstepSource <*> pTerm rhs <*> fctxt <*> (pair <$> flstate <*> frstate) <*>
        return ins <*> return out <*> return signals
    where fstepSource = case lhs of App "Name" _ -> return Nothing
                                    App "NameApp" [_,term] -> pMaybePatterns term
          fctxt = case mctxt of  App "None" _ -> return []
                                 App "Some" [App "Context" [List inhs]] ->
                                    mapM op inhs
            where op (App "Inherited"[String nm, pat]) = (\p-> (nm,p)) <$> pGroupPattern pat
          femitted = case mline of
                        App "NormalNoEmitted" _ -> return ([],[],[])
                        App "NormalEmitted" [List emits] -> foldM pEmitted ([],[],[]) emits
          flstate = mapM op lstate
            where op (App "Mutable" [String nm, term]) = (\t -> (nm,t)) <$> pGroupPattern term
          frstate = mapM op rstate
            where op (App "Mutable" [String nm, term]) = (\t -> (nm,t)) <$> pTerm term

          pEmitted (signs, ins, outs) (App "Emitted" [String nm,mpolarity,term]) =
            case mpolarity of
                App "None" _ -> do  pterm <- pTerm term
                                    return ((nm,pterm):signs,ins,outs)
                App "Some" [String "!"] -> do
                    pterm <- pTerm term
                    return (signs,ins,(nm,pterm):outs)
                App "Some" [String "?"] -> do
                    pat <- pPattern term
                    return (signs,(nm,pat):ins, outs)

premiseStep :: ATerm -> ATerm -> [ATerm] -> ATerm -> ATerm -> [ATerm] -> Feedback FPremiseStep
premiseStep mctxt lhs lstate mline rhs rstate = do
    (signals, ins, out) <- femitted
    FPremiseStep <$> pTerm lhs <*> pGroupPattern rhs <*> fctxt <*>
        (pair <$> flstate <*> frstate) <*> return ins <*> return out <*> return signals
    where fctxt = case mctxt of  App "None" _ -> return []
                                 App "Some" [App "Context" [List inhs]] ->
                                    mapM op inhs
            where op (App "Inherited" [String nm, term]) =(\p-> (nm,p))<$> pTerm term
          femitted = case mline of
                       App "NormalNoEmitted" _ -> return ([],[],[])
                       App "NormalEmitted" [List emits] -> foldM pEmitted ([],[],[]) emits

          flstate = mapM op lstate
            where op (App "Mutable" [String nm, term]) = (\t -> (nm,t)) <$> pTerm term
          frstate = mapM op rstate
            where op (App "Mutable" [String nm, term]) = (\t -> (nm,t)) <$> pGroupPattern term

          pEmitted (signs, ins, outs) (App "Emitted" [String nm,mpolarity,pat]) =
            case mpolarity of
                App "None" _ -> do  ppat <- pPattern pat
                                    return ((nm,ppat):signs,ins,outs)
                App "Some" [String "!"] -> do
                    ppat <- pPattern pat
                    return (signs,ins,(nm,ppat):outs)
                App "Some" [String "?"] -> do
                    term <- pTerm pat
                    return (signs,(nm,term):ins, outs)

pDataTypeAlts :: Name -> Builder [DataTypeAlt]
pDataTypeAlts nm aterms = catMaybes <$> mapM (pDataTypeAlt nm) aterms

pDataTypeAlt :: Name -> Parser (Maybe DataTypeAlt)
pDataTypeAlt nm (App "Dots" _) = do
    warn_ ("Datatype " ++ nm ++ " without definition")
    return Nothing
pDataTypeAlt nm (App "Injection" [_,ty]) = Just . DataTypeInclusion <$> pTerm ty
pDataTypeAlt _ (App "Constructor" [String nm, mparams]) = do
    params <- case mparams of
                App "None" _ -> return []
                App "Some" [App "Params" [List pars]] -> mapM dataValSort pars
    return $ Just $ DataTypeConstructor nm params
 where dataValSort (App "Param" [_, mty]) = case mty of
            App "None" _ -> fError ("parameters of constructor " ++ nm ++ " do not have types")
            App "Some" [ty] -> pTerm ty
       dataValSort _ = fError "unknown datatype definition"

pComments :: [ATerm] -> String
pComments = concatMap pComment

pComment :: ATerm -> String
pComment (App "Ordinary" [String str]) = str
pComment (App "Asterisk" _) = "*"
pComment (App "At" _) = "@"
pComment (App "Term" [App "TermDots" _]) = "..."
pComment (App "Term" [term]) = "/" ++ ppTerm term ++ "/ "
pComment (App "Formula" _) = "<missing-formula>"
pComment (App "Spec" _) = "<missing-spec>"
pComment (App "SNum" _) = "<missing-section-nr>"
pComment _ = ""

-- pretty print terms directly
ppTerms :: ATerm-> String
ppTerms (App "Sequence" [tm, terms]) = ppTerm tm ++ "," ++ ppTerms terms
ppTerms t = ppTerm t

ppTerm :: ATerm -> String
ppTerm (App "TermDots" _) = "..."
ppTerm (App "Typed" [term,ty]) = ppTerm term -- ignores types of typed terms
ppTerm (App "EmptyList" _) = "[]"
ppTerm (App "List" [sequence]) = "[" ++ ppTerms sequence ++ "]"
ppTerm (App "Name" [String nm]) = nm
ppTerm (App "NameApp" [String nm, term]) = nm ++ ppTerm term
ppTerm (App "Group" [terms]) = "(" ++ ppTerms terms ++ ")"
ppTerm (App "EmptyGroup" _) = "()"
ppTerm (App "TermVar" [name]) = ppMetaVar name
--ppTerm (App "Sequence" [term1,term2]) = (\a b -> TTuple (a ++ [b])) <$> ppTerms term1 <*> ppTerm term2
ppTerm (App "Computes" [to]) = "=>" ++ ppTerm to
ppTerm (App "ComputesFrom" [from,to]) =  ppTerm from ++ "=>" ++ ppTerm to
ppTerm (App "Postfix" [ty, String op]) = ppTerm ty ++ op
ppTerm (App "Set" [terms]) = "{" ++ ppTerms terms ++ "}"
ppTerm (App "Map" [List kvs]) = "{" ++ intercalate "," (map op kvs) ++ "}"
    where op (App "Point" [key,value]) = ppTerm key ++ " |-> " ++ ppTerm value
ppTerm (App "Const" [String str]) = str
ppTerm seq@(App "Sequence" _) = ppTerms seq
ppTerm (App "Union" [term1,List [term2]]) = ppTerm term1 ++ "|" ++ ppTerm term2
ppTerm (App "VarApp" [var, term]) = ppMetaVar var ++ ppTerm term
ppTerm aterm = error ("missing in ppTerm: " ++ show aterm)

ppMetaVar (App "VarStem" [String var, String suffix, App "Some" [String postfix]]) =
              var ++ suffix ++ postfix
ppMetaVar (App "VarStem" [String var, String suffix, _]) = var ++ suffix
ppMetaVar (App "Wild" _) = "_"

-- builders

bFSig :: Maybe [ATerm]  -> Builder FSig
bFSig mdoc [String nm, mparams, mcomptype] = do
    comptype <- pFSort mcomptype
    params <- pSigParams mparams
    case mdoc of
        Nothing -> return (FSig nm params comptype Nothing)
        Just cs -> return (FSig nm params comptype (Just (pComments cs)))
bFSig _ args = fError ("cannot build fsig: " ++ show args)

bFSpec :: FSig -> [[ATerm]] -> Builder FunconSpec
bFSpec sig [] [_, mparams, App "TypeValue" [_, term]] = FAbbrv sig <$> pTerm term
bFSpec sig@(FSig nm _ _ _) mrules _ = FRules sig <$> mapM (bRule nm) mrules

pSigParams :: Parser [(ParamPattern, FSorts)]
pSigParams aterm = case aterm of
    (App "None" []) -> return []
    (App "Some" [App "Params" [List params]]) -> mapM pSigParam params
 where  pSigParam (App "Param" [name, App "None" _]) =
            fError "parameter in signature should have an annotation"
        pSigParam (App "Param" [name, App "Some" [constraint]])
            = do    sorts <- pFSorts constraint
                    pattern <- getParamPattern name
                    return $ (pattern, sorts)
        pSigParam (App "TypeParam" [name, tconstraint])
            = fError ("TODO Param.TypeParam")
        pSigParam arg = fError ("missing case for pSigParam: " ++ show arg)

pFSorts (App "Type" [constraint]) = pFSorts constraint
pFSorts (App "Postfix" [ty, String op]) = FSequenceSort <$> pFSort ty <*> pPostfix op
pFSorts ty = FSingletonSort <$> pFSort ty

pValSorts :: Parser FValSorts
pValSorts (App "Type" [constraint]) = pValSorts constraint
pValSorts (App "Postfix" [ty, String op]) = FSequenceValSort <$> pTerm ty <*> pPostfix op
pValSorts ty = FSingletonValSort <$> pTerm ty

bRule :: Name -> Builder FRule
-- rewrite without bar, no side-conditions
bRule nm [App "Axiom" [(App "Equation" [App "NameApp" [String x, lhsterm], rhsterm])]] =
  FRuleRewrite x <$> pMaybePatterns lhsterm <*> pTerm rhsterm <*> return []
-- rewrite with bar and side-conditions
bRule nm [App "Inference" [List prems,_,App "Equation"
            [App "NameApp" [String x, pats],term]]] =
  FRuleRewrite nm <$> pMaybePatterns pats <*> pTerm term <*> (rights <$> pSideConditions prems)
-- step without premises (no bar)
bRule nm [App "Axiom" [(App "Eval" [mcontext, lhs, line, rhs])]] =
    FRuleStep nm <$> evalStep mcontext lhs [] line rhs [] <*> return []
-- step without premises (no bar), with mutable entities
bRule nm [App "Axiom" [(App "Effect" [mcontext, App "State" [lhs,List lstate], line,
        App "State" [rhs,List rstate]])]] =
    FRuleStep nm <$> evalStep mcontext lhs lstate line rhs rstate <*> return []
-- step with bar, no mutable entities
bRule nm [App "Inference" [List prems,_,App "Eval" [mcontext, lhs, line, rhs]]]
 = FRuleStep nm <$> evalStep mcontext lhs [] line rhs [] <*> pSideConditions prems
-- step with bar, mutable entities
bRule nm [App "Inference" [List prems,_,App "Effect" [mcontext, App "State" [lhs, List lstate]
    , line, App "State" [rhs, List rstate ]]]]
 = FRuleStep nm <$> evalStep mcontext lhs lstate line rhs rstate <*> pSideConditions prems
bRule nm aterm = fError ("missing case for bRule: " ++ show aterm)

-- helpers
pair a b = (a,b)

getParamPattern (App "Wild" _) = return PPAny
getParamPattern (String "_") = return PPAny
getParamPattern str = do  (var, mop) <- getMetaVar str
                          case mop of
                            Just op -> return $ PPSeqMetaVar var op
                            _       -> return $ PPMetaVar var


getMetaVar :: Parser (String, Maybe SeqSortOp)
getMetaVar (String var) = return (var, Nothing)
getMetaVar (App "VarStem" [String var, String suffix, App "Some" [String postfix]]) =
    (var ++ suffix ++ postfix,) . Just <$> pPostfix postfix
getMetaVar (App "VarStem" [String var, String suffix, _]) = return (var ++ suffix, Nothing)
getMetaVar (App "Wild" _) = return ("_", Nothing)

fError = errorMessage . wrapped

findsCons :: String -> [ATerm] -> [[ATerm]]
findsCons str = map (findCons str)

findCons :: String -> ATerm -> [ATerm]
findCons str (App con aterms) | con == str = aterms
                              | otherwise  = concatMap (findCons str) aterms
findCons str (Tuple aterms) = concatMap (findCons str) aterms
findCons str (List aterms) = concatMap (findCons str) aterms
findCons str (Ann _ aterms) = concatMap (findCons str) aterms
findCons _ _ = []

{-
deriving instance Show FSpec
deriving instance Show FSig
deriving instance Show FRule
deriving instance Show FSorts
deriving instance Show FTerm
deriving instance Show FLiteral
deriving instance Show FSideCondition
deriving instance Show SeqSortOp
deriving instance Show FPattern
deriving instance Show FSort
deriving instance Show FValSort
-}
