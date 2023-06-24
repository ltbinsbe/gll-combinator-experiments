{-# Language FlexibleContexts, ScopedTypeVariables, LambdaCase
        , MultiParamTypeClasses, TupleSections, FlexibleInstances #-}

module Simplify.TargetToFunconModules where

import Control.Arrow ((***))
import CCO.Component (Component, component)
import Data.Text (pack)

--------------------------------------------------------------------
import Funcons.EDSL (type_, Funcons(FValue), Values(..), FTerm(..), string__, DataTypeMembers(..), DataTypeAltt(..), pat2term)
import Types.SourceAbstractSyntax (Name, FLiteral(..))
import Types.CoreAbstractSyntax (FSig(..), FTerm(TSeq), funconIsNullary, ConsSpec(..), DataTypeSpec(..), DataTypeAlt(..))
import Types.TargetAbstractSyntax
import qualified Types.FunconModule as F
import Simplify.Utils
--------------------------------------------------------------------

-- require for forming a pipeline with uu-cco library
target2fmodule :: Bool -> Component CBSFile F.FunconModule
target2fmodule gen_ph = component (return . simplifyCBSFile gen_ph)

simplifyCBSFile :: Bool -> CBSFile -> F.FunconModule
simplifyCBSFile gen_ph cbsfile = 
    let fspecs = concatMap (simplifyFunconSpec gen_ph) (funcons cbsfile)
    in F.FunconModule fspecs
          (entities cbsfile) 
          (map (gTypeMember (constructors cbsfile)) (datatypes cbsfile))
          (env cbsfile)
          (aliases cbsfile)

gTypeMember :: [ConsSpec] -> DataTypeSpec -> DataTypeMembers
gTypeMember css (DataTypeDecl nm typarams alts) = 
  DataTypeMemberss (pack nm) typarams (concatMap gAlts alts ++ gCons)
  where gAlts (Types.CoreAbstractSyntax.DataTypeInclusion term) = 
          [Funcons.EDSL.DataTypeInclusionn term]
        gCons = foldr op [] css
          where op (ValCons cons _ args nm' tparams) acc
                  | nm == nm' = Funcons.EDSL.DataTypeMemberConstructor (pack cons) args (Just tparams):acc
                  | otherwise = acc

simplifyFunconSpec :: Bool -> FunconSpec -> [F.FunconSpec]
simplifyFunconSpec gen_ph (FRules _ _ _ [] [])
  | not gen_ph = [] -- remove funcons without rules
simplifyFunconSpec _ (FRules nm sig mdoc rewrites steps) = 
    let rewrites' = map (simplifyRewriteRule sig) rewrites
        steps'    = map (simplifyStepRule sig) steps
    in [F.FunconSpec nm sig mdoc rewrites' steps']

simplifyRewriteRule :: FSig -> FRewriteRule -> [F.FRewriteStmt]
simplifyRewriteRule sig (FRewriteRule pats mterm sides) = 
    source ++ sideconditions ++ [target]
 where  source  | funconIsNullary sig   = []
                | otherwise             = [F.ArgsPattern F.fargs_var pats]
        sideconditions = map F.CheckSideCondition sides
        target = F.RewriteTarget (maybe (TSeq []) id mterm)

simplifyStepRule ::  FSig -> FStepRule -> [F.FStepStmt]
simplifyStepRule sig (FStepRule fstep e_prem_sides) = 
    source_pat ++
    source_mut_ps ++
    source_inhs ++ 
    source_inps ++ 
    source_dsigs ++
    bar ++
    target_ctrls ++
    target_outs ++
    source_mut_ts ++
    [target]
    where   source_pat  
              | funconIsNullary sig = [] 
              | otherwise           = [F.FRewriteStmt(F.ArgsPattern F.fargs_var pats)]
                where pats = stepSource fstep
            target = F.StepTarget (stepTarget fstep)
            source_inhs = map (uncurry F.ReadInherited)
                            (stepInheritedEntities fstep)
            (source_mut_ps,source_mut_ts) = 
              foldr op ([],[]) (stepMutableEntities fstep)
              where op (nm,p,t) (ps,ts) = (F.ReadMutable nm p:ps
                                          ,F.WriteMutable nm t:ts)
            source_inps = map (uncurry F.ReadInput) (stepInputEntities fstep) 
            source_dsigs = map (uncurry F.ReadDownControl) (stepControlEntities fstep)
            target_outs = map (uncurry F.WriteOutput) (stepOutputEntities fstep)
            target_ctrls = map (uncurry F.WriteControl) 
                                (map (id *** fmap pat2term) $ stepControlEntities fstep)
            bar = concatMap sel e_prem_sides
                where   sel (Right side) = [F.FRewriteStmt 
                                                (F.CheckSideCondition side)]
                        sel (Left prem)  = premToStmts prem

            premToStmts prem = muts_ts ++ [premise] ++ sigReads ++ muts_ps
             where  (muts_ts,muts_ps) = foldr op ([],[]) (premiseMutableEntities prem)
                      where op (nm,t,p) (ts,ps) = (F.WriteMutable nm t:ts
                                                  ,F.ReadMutable nm p:ps)
                    sigReads = map op (premiseControlEntities prem)
                     where op (nm,mpat) = F.ReadControl nm mpat
                    premise =  
                        -- receive
                        flip (foldr out_op) (premiseOutputEntities prem) $
                        receiveControl (premiseControlEntities prem) $
                        -- scope
                        flip (foldr dsigs_op) (premiseControlEntities prem) $
                        flip (foldr inhs_op) (premiseInheritedEntities prem) $
                        flip (foldr inps_op) (premiseInputEntities prem) $
                            (F.Premise (premiseSource prem) 
                                (premiseTarget prem))
                     where 
                        out_op :: (Name,FPattern) -> F.FStepStmt -> F.FStepStmt
                        out_op (nm,pat) = F.ReceiveOutput nm pat

                        inps_op :: (Name, [FTerm], InputAccess) -> F.FStepStmt 
                                    -> F.FStepStmt
                        inps_op (nm, fcts, acc) = F.ScopeInput nm fcts acc
                                
                        inhs_op :: (Name, FTerm) -> F.FStepStmt -> F.FStepStmt
                        inhs_op (nm, fct) = F.ScopeInherited nm fct 
            
                        dsigs_op :: (Name, Maybe FPattern) -> F.FStepStmt -> F.FStepStmt
                        dsigs_op (nm, fct) = F.ScopeDownControl nm (fmap pat2term fct)

                        receiveControl ents 
                            | null ents = id
                            | otherwise =  F.ReceiveControl (map fst $ ents)

