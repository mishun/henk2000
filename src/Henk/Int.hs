module Henk.Int
    ( intmain
    , prog2DeltaRules
    , reduce_to_whnf
    , reduce_to_nf
    ) where

import Data.Maybe (fromMaybe)
import Control.Monad (mplus)
import Henk.AS
import Henk.PP (expr2string)
import Henk.TermSupport


--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------
intmain :: DeltaRules -> Program -> IO Expr
intmain deltaRules _ = do
    let ex = case tryReduceRedex deltaRules (VarExpr (TVar (Var "main") Unknown)) of
                 Nothing   -> error "main not defined"
                 Just main -> main

    putStrLn $ "\nEvaluating: \n" ++ expr2string ex
    let nf = reduce_to_mnf deltaRules ex
    putStrLn $ "Result: " ++ expr2string nf
    return nf


--------------------------------------------------------------------------------
-- Delta Rules
--------------------------------------------------------------------------------                                 
prog2DeltaRules :: Program -> DeltaRules
prog2DeltaRules (Program _ vdecls) = map vDecl2DeltaRule vdecls


vDecl2DeltaRule :: VDecl -> DeltaRule
vDecl2DeltaRule (VDecl tv ex)  = DeltaRule tv ex


lookup'' :: TVar -> DeltaRules -> Maybe DeltaRule
lookup'' tv@(TVar (Var v) _) (r@(DeltaRule ex1 _):rs) =
    case ex1 of
        (TVar (Var v1) _) | (v1==v)   -> Just r
                          | otherwise -> lookup'' tv rs
        _                             -> undefined
lookup'' _ _ = Nothing


--------------------------------------------------------------------------------
-- Reducing Redexes
--------------------------------------------------------------------------------

tryReduceRedex :: DeltaRules -> Expr -> Maybe Expr
tryReduceRedex _ (AppExpr (LamExpr tv ex1) ex2) =
    return $ applySubst [(Sub tv ex2)] ex1

tryReduceRedex dr ce@(CaseExpr ex alts _) =
    let whnf' = reduce_to_whnf dr ex
    in case lookupA whnf' alts of
        Just (Alt tc tcas dcas res) -> return $ applySubToLeftMost [Sub tc (foldr LamExpr res (tcas ++ dcas))] whnf'
        Nothing                     ->
            error $ "runtime error: missing alternative (" ++ expr2string (leftMost whnf') ++ ") in case expression " ++ expr2string ce

tryReduceRedex dr (VarExpr tv) = do
    DeltaRule _ ex2 <- lookup'' tv dr
    return ex2

tryReduceRedex _ _ = Nothing


lookupA :: Expr -> [Alt] -> Maybe Alt
lookupA ex alts = lookupA' (leftMost ex) alts


lookupA' :: Expr -> [Alt] -> Maybe Alt
lookupA' ex ((a@(Alt  (TVar va _) _ _ _)) : as) =
    case ex of
        (VarExpr (TVar v _))  | v == va    -> Just  a
                              | otherwise  -> lookupA' ex as
        _                                  -> undefined
lookupA' _ [] = Nothing


--------------------------------------------------------------------------------
-- eval Reduction
--------------------------------------------------------------------------------
-- The result of a reduction of the main function should be a data object 
-- (no function). So it only makes sense to reduce inner redexes if there are
-- only variables left of them.


eval :: DeltaRules -> Expr -> Maybe Expr
eval dr ex | Just reduced <- tryReduceRedex dr ex  = return $ fromMaybe reduced $ eval dr reduced
eval dr (AppExpr ex1 ex2) =
    case eval dr ex1 of
        Just ex1r -> return $ fromMaybe (AppExpr ex1r ex2) $ eval dr $ AppExpr ex1r ex2
        Nothing   -> AppExpr ex1 `fmap` eval dr ex2
eval _ _ = Nothing


-- Reducing using the normal strategy until a "eval" head normal form is reached                              
reduce_to_mnf :: DeltaRules -> Expr -> Expr
reduce_to_mnf dr ex = fromMaybe ex $ eval dr ex 
   
	                    
--------------------------------------------------------------------------------
-- Weak Reduction
--------------------------------------------------------------------------------                                         
-- weak performes normal order reduction steps until 
-- a weak head normal formal is reached
-- normal order = left-most outer-most


weak :: DeltaRules -> Expr -> Maybe Expr
weak dr ex | Just reduced <- tryReduceRedex dr ex  = return $ fromMaybe reduced $ weak dr reduced
weak dr (AppExpr ex1 ex2) = do
    ex1r <- weak dr ex1
    return $ fromMaybe (AppExpr ex1r ex2) $ weak dr $ AppExpr ex1r ex2
weak _ _ = Nothing


-- Reducing using the normal strategy until a weak head normal form is reached
reduce_to_whnf :: DeltaRules -> Expr -> Expr
reduce_to_whnf dr ex = fromMaybe ex $ weak dr ex


--------------------------------------------------------------------------------
-- Strong Reduction
--------------------------------------------------------------------------------
-- we do not need strong reduction for interpreting Henk-programs, however
 -- in the type checker we need to check whether types are Beta-equivalent.
-- Because recursion is not allowed on the level of types, types will
-- always reduce to a (unique) nf. Therefore we can check whether two
-- types are Beta-equivalent, by reducing them both to a nf, and checking
-- if they are syntacticly equivalent modulo alpha-conversion.

strong :: DeltaRules -> Expr -> Maybe Expr
strong dr (AppExpr (LamExpr tv ex1) ex2) =
    let reduced = applySStrongSubst (Sub tv ex2) ex1
    in return $ fromMaybe reduced $ strong dr reduced
strong dr ex | Just reduced <- tryReduceRedex dr ex  = return $ fromMaybe reduced $ strong dr reduced
strong dr (AppExpr ex1 ex2) =
    case strong dr ex1 of 
        Just ex1r -> return $ fromMaybe (AppExpr ex1r ex2) $ strong dr $ AppExpr ex1r ex2
        Nothing   -> AppExpr ex1 `fmap` strong dr ex2
strong dr (LamExpr (TVar var exv) ex) =
    if mexvr == Nothing && mexr == Nothing
        then Nothing
        else return $
            let exvr = fromMaybe exv mexvr
                exr  = fromMaybe ex mexr
            in LamExpr (TVar var exvr) exr
    where  
        mexvr = strong dr exv
        mexr  = strong dr ex
strong _ _ = Nothing


-- Reducing using the normal strategy until a normal form is reached
reduce_to_nf :: DeltaRules -> Expr -> Expr
reduce_to_nf dr ex =
    let mnf = reduce_to_mnf dr ex
    in fromMaybe ex $ mplus (strong dr mnf) (Just mnf)

