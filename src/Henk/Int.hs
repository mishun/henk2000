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
intmain deltaRules _
  = do{ex     <- case lookup'' (TVar (Var "main") Unknown) deltaRules of
                  Just deltarule -> return $ (reduceRedex deltaRules (DeltaRedex deltarule) (VarExpr $ TVar (Var "main") Unknown))
                  Nothing         -> error "main not defined!!"                     
      ;putStr $ "\nEvaluating: \n" ++ expr2string ex ++ "\n\n"
      ;nf     <- return $ reduce_to_mnf deltaRules ex
      ;putStr $ "Result: \n" ++ expr2string nf
      ;return nf
      }


--------------------------------------------------------------------------------
-- Delta Rules
--------------------------------------------------------------------------------                                 
prog2DeltaRules :: Program -> DeltaRules
prog2DeltaRules (Program _ vdecls) = map vDecl2DeltaRule vdecls


vDecl2DeltaRule :: VDecl -> DeltaRule
vDecl2DeltaRule (VDecl tv ex)  = DeltaRule tv ex


--------------------------------------------------------------------------------
-- Reducing Redexes
--------------------------------------------------------------------------------
reduceRedex :: DeltaRules -> RedexInf -> Expr -> Expr
reduceRedex dr ri ex = case ri of
    BetaRedex      -> reduceBeta ex
    CaseRedex      -> reduceCase dr ex
    DeltaRedex dr1 -> reduceDeltaRule ex dr1
    NoRedex        -> error "NoRedex"

reduceBeta :: Expr -> Expr
reduceBeta (AppExpr  (LamExpr tv ex1) ex2) = applySubst [(Sub tv ex2)] ex1  		      
reduceBeta _ = undefined

reduceCase :: DeltaRules -> Expr -> Expr
reduceCase dr ce@(CaseExpr ex alts _) =
 case lookupA whnf' alts of
  Just (Alt tc tcas dcas res) -> applySubToLeftMost [Sub tc (foldr LamExpr res (tcas++dcas))] whnf'
  Nothing                     -> error $ "runtime error: missing alternative (" ++ expr2string (leftMost whnf') ++") in case expression!!\n" ++ (expr2string ce)
 where whnf' = reduce_to_whnf dr ex
reduceCase _ _ = undefined

lookupA :: Expr -> [Alt] -> Maybe Alt
lookupA ex alts = lookupA' (leftMost ex) alts

lookupA' :: Expr -> [Alt] -> Maybe Alt
lookupA' ex ((a@(Alt  (TVar va _) _ _ _)) : as) =
    case ex of
        (VarExpr (TVar v _))  | v==va      -> Just  a
                              | otherwise  -> lookupA' ex as
        _                                  -> undefined
lookupA' _ [] = Nothing





reduceDeltaRule :: Expr -> DeltaRule -> Expr
reduceDeltaRule _ (DeltaRule _ ex2) = ex2

--------------------------------------------------------------------------------
-- eval Reduction
--------------------------------------------------------------------------------
-- The result of a reduction of the main function should be a data object 
-- (no function). So it only makes sense to reduce inner redexes if there are
-- only variables left of them.


eval :: DeltaRules -> Expr -> Maybe Expr
eval dr ex | redexinf /= NoRedex  = mplus (eval dr reduced) (Just reduced)
    where redexinf = isRedex dr ex
          reduced  = reduceRedex dr redexinf ex

eval dr (AppExpr ex1 ex2) =
    case eval dr ex1 of
        Just ex1r -> mplus (eval dr $ AppExpr ex1r ex2) (Just $ AppExpr ex1r ex2)
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
weak dr ex | redexinf /= NoRedex  = mplus (weak dr reduced) (Just reduced)
    where redexinf = isRedex dr ex
          reduced  = reduceRedex dr redexinf ex

weak dr (AppExpr ex1 ex2) = do
    ex1r <- weak dr ex1
    mplus (weak dr $ AppExpr ex1r ex2) (Just $ AppExpr ex1r ex2)

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
strong dr ex | not $ redexinf `elem` [NoRedex, BetaRedex]  = mplus (strong dr reduced) (Just reduced)
             | redexinf == BetaRedex                       =
        let (AppExpr (LamExpr tv ex1) ex2) = ex
            breduced = applySStrongSubst (Sub tv ex2) ex1
        in mplus (strong dr breduced) (Just breduced)
    where redexinf = isRedex dr ex
          reduced  = (reduceRedex dr redexinf ex)

strong dr (AppExpr ex1 ex2) =
    case strong dr ex1 of 
        Just ex1r -> mplus (strong dr $ AppExpr ex1r ex2) (Just $ AppExpr ex1r ex2)
        Nothing   -> AppExpr ex1 `fmap` strong dr ex2

strong dr (LamExpr (TVar var exv) ex) =
    if (mexvr==Nothing && mexr==Nothing)
        then Nothing
        else do
            exvr <- mplus mexvr (Just exv)
            exr <- mplus mexr (Just ex)
            return $ LamExpr (TVar var exvr) exr
    where  
        mexvr = strong dr exv
        mexr  = strong dr ex

strong _ _ = Nothing


-- Reducing using the normal strategy until a normal form is reached
reduce_to_nf :: DeltaRules -> Expr -> Expr
reduce_to_nf dr ex =
    let mnf = reduce_to_mnf dr ex
    in fromMaybe ex $ mplus (strong dr mnf) (Just mnf)

