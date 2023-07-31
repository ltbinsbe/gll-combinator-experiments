{-# LANGUAGE OverloadedStrings #-}

module Types.Examples where

import Types.SourceAbstractSyntax

{-
Funcon
  effect(_:values) : =>()
    := ()
-}
effectSpec :: FSpec
effectSpec =
  FAbbrv
    (FSig "effect"
          [(Nothing, FSingletonSort (FValSort (FName "values")))]
          (FCompSort (FTuple []))
    )
    (FTuple [])

{-
Funcon
  set-map(F:S=>T,S:sets(S)) : =>sets(T)
    := list-to-set(list-map(F,set-to-list(S)))
-}
setMapSpec :: FSpec
setMapSpec =
  FAbbrv
    (FSig "set-map"
          [ (Just "F", FSingletonSort (FCompFromSort (FMetaVar "S") (FMetaVar "T")))
          , (Just "S", FSingletonSort (FValSort (FApp "sets" (FMetaVar "S"))))
          ]
          (FCompSort (FApp "sets" (FMetaVar "T")))
    )
    (FApp "list-to-set" (FApp "list-map" (FTuple [FMetaVar "F", FApp "set-to-list" (FMetaVar "S")])))

{-
Funcon
  sequential(Xs:(=>values)*) : =>(values*)
    := discard-empty-tuples(left-to-right(Xs))
-}
sequentialSpec :: FSpec
sequentialSpec =
  FAbbrv
    (FSig "sequential"
          [(Just "X*", FSequenceSort (FCompSort (FName "values")) FStarOp)]
          (FCompSort (FSortTupleSeq (FName "values") FStarOp))
    )
    (FApp "discard-empty-tuples" (FApp "left-to-right" (FMetaVar "X*")))

{-
Funcon
  if-then-else(_:booleans, _:=>T, _:=>T) : =>T
Rule
  if-then-else(true, X, _) = X
Rule
  if-then-else(false, _, Y) = Y
-}
ifThenElseSpec :: FSpec
ifThenElseSpec =
  FRules
    (FSig "if-then-else"
          [ (Nothing, FSingletonSort (FValSort (FName "booleans")))
          , (Nothing, FSingletonSort (FCompSort (FMetaVar "T")))
          , (Nothing, FSingletonSort (FCompSort (FMetaVar "T")))
          ]
          (FCompSort (FMetaVar "T"))
    )
    [ FRuleRewrite "if-then-else" (Just [PADT "true" [], PMetaVar "X", PAny]) (FMetaVar "X") []
    , FRuleRewrite "if-then-else" (Just [PADT "false" [], PAny, PMetaVar "Y"]) (FMetaVar "Y") []
    ]
    Nothing

{-
Funcon
  list-map(_:S=>T,_:lists(S)) : =>lists(T)
Rule
  list-map(F,[]) = []
Rule
         head(L) = H         tail(L) = T
  -------------------------------------------------------------
  list-map(F,L) = cons(left-to-right(give(H,F), list-map(F,T)))
-}
listMapSpec :: FSpec
listMapSpec =
  FRules
    (FSig "list-map"
          [ (Nothing, FSingletonSort (FCompFromSort (FMetaVar "S") (FMetaVar "T")))
          , (Nothing, FSingletonSort (FValSort (FApp "lists" (FMetaVar "S"))))
          ]
          (FCompSort (FApp "lists" (FMetaVar "T")))
    )
    [ FRuleRewrite "list-map"
                   (Just [PMetaVar "F", PList []])
                   (FList [])
                   []
    , FRuleRewrite "list-map"
                   (Just [PMetaVar "F", PMetaVar "L"])
                   (FApp "cons" (FApp "left-to-right" (FTuple [ FApp "give" (FTuple [FMetaVar "H", FMetaVar "F"])
                                                                     , FApp "list-map" (FTuple [FMetaVar "F", FMetaVar "T"])])))
                   [ EvaluationSideCondition (FApp "head" (FMetaVar "L")) (PMetaVar "H")
                   , EvaluationSideCondition (FApp "tail" (FMetaVar "L")) (PMetaVar "T")
                   ]
    ]
    Nothing

{-
Funcon
  bound(_:binders) : =>values
Rule
          lookup(Rho,B) = V
  -----------------------------------
  environment(Rho) |- bound(B) ---> V
Rule
    is-in-set(B,domain(Rho)) == false
  --------------------------------------
  environment(Rho) |- bound(B) ---> fail
-}
boundSpec :: FSpec
boundSpec =
  FRules
    (FSig "bound"
          [ (Nothing, FSingletonSort (FValSort (FName "binders")))
          ]
          (FCompSort (FName "values"))
    )
    [ FRuleStep "bound"
                FStep { stepSource            = Just [PMetaVar "B"]
                      , stepTarget            = FMetaVar "V"
                      , stepInheritedEntities = [("environment",PMetaVar "Rho")]
                      , stepMutableEntities   = ([],[])
                      , stepInputEntities     = []
                      , stepOutputEntities    = []
                      , stepControlEntities   = []
                      }
                [Right (EvaluationSideCondition (FApp "lookup" (FTuple [FMetaVar "Rho", FMetaVar "B"])) (PMetaVar "V"))]
    , FRuleStep "bound"
                FStep { stepSource            = Just [PMetaVar "B"]
                      , stepTarget            = FName "fail"
                      , stepInheritedEntities = [("environment",PMetaVar "Rho")]
                      , stepMutableEntities   = ([],[])
                      , stepInputEntities     = []
                      , stepOutputEntities    = []
                      , stepControlEntities   = []
                      }
                [Right (EqualitySideCondition (FApp "is-in-set" (FTuple [FMetaVar "B", FApp "domain" (FMetaVar "Rho")])) (FName "false"))]
    ]
    Nothing
