module Henk.TC
    ( tcmain
    , tcexpr
    ) where

import Control.Monad (unless, forM)
import Henk.AS
import Henk.PP (tVar2string, expr2string)
import Henk.Int (reduce_to_whnf, reduce_to_nf)
import Henk.TermSupport (DeltaRules, equal, leftMost, SSubst(..), applySSubst, applySubst)
import Henk.Classification (rho, sortt, elmt)
import Henk.TypeSystems (Specification)


--------------------------------------------------------------------------------  
-- The Type Check Monad
-------------------------------------------------------------------------------- 
type Error       = String
type Errors      = [Error]

newtype TC t = TC (Errors, t)

instance Monad TC where
 return x    = TC ([], x)
 f >>= g     = TC (let TC (erf, x)     = f 
                       TC (erg, y)     = g x
                   in (erf ++ erg, y))

runTC        :: TC a -> (Errors, a)
runTC (TC (er, result)) = (er, result)


tcmain :: DeltaRules -> Specification -> Program -> (Errors, ())
tcmain dr sp p = runTC (program dr sp p)

tcexpr :: DeltaRules -> Specification -> Expr -> (Errors, Expr)
tcexpr dr sp ex = runTC (expr dr sp ex)

addErrorMsg :: String -> TC ()
addErrorMsg s = TC ([s], ())


type TypeCheck a b = DeltaRules -> Specification -> a -> TC b


--------------------------------------------------------------------------------  
-- Program
--------------------------------------------------------------------------------
program :: TypeCheck Program ()
program  dr sp (Program tds vds) = do
    mapM_ (tDecl dr sp) tds
    mapM_ (vDecl dr sp) vds
    return ()

--------------------------------------------------------------------------------  
-- Type Declarations
--------------------------------------------------------------------------------
tDecl :: TypeCheck TDecl ()
tDecl dr sp td@(TDecl tv tvs) = do
    mapM_ (\ (TVar _ t) -> expr dr sp t) (tv : tvs)
    isOfRightForm dr sp td
    return ()


isOfRightForm :: TypeCheck TDecl ()
isOfRightForm _ _ _ = return ()
-- should check whether the ADT is of the form
-- described in definition 3.2 of the thesis
-- but is not yet implemented

--------------------------------------------------------------------------------  
-- Value Declarations
--------------------------------------------------------------------------------
vDecl    :: TypeCheck VDecl ()
vDecl dr sp (VDecl tv@(TVar _ tv_type) ex) = do
    ex_type <- expr dr sp ex
    unless (equal tv_type ex_type) $
        addErrorMsg $ bindMsg tv tv_type ex ex_type

                                 
--------------------------------------------------------------------------------  
-- Expressions
--------------------------------------------------------------------------------                                                                                     
exprwh :: TypeCheck Expr Expr
exprwh dr sp ex' = do
    ex <- expr dr sp ex'
    return $ reduce_to_whnf dr ex


expr :: TypeCheck Expr Expr

expr _ (_, a, _) (SortExpr s1) =
    case lookup s1 a of
        Just s2 -> return $ SortExpr s2
        Nothing -> do
            addErrorMsg $ noAxiomMsg s1
            return Unknown

expr _ _ (VarExpr (TVar _ ex)) = return ex

expr dr sp@(_, _, r) ex@(PiExpr (TVar _ a) b) = do
    btype <- exprwh dr sp b
    case sortt sp (Just a)  of 
        Nothing -> do
            addErrorMsg $ noSortAMsg ex
            return Unknown
        Just s1  ->
            case btype of
                SortExpr s2 ->
                    case lookup' (s1,s2) r of
                        Nothing         -> do
                            addErrorMsg $ ruleMsg ex s1 s2  
                            return Unknown
                        Just (_, _, s3) ->
                            return $ SortExpr s3
                _           -> do
                    addErrorMsg $ noSortBMsg ex btype
                    return Unknown

expr dr sp ex@(LamExpr tv@(TVar _ a) m) = do
    b <- expr dr sp m                  
    case rho sp (sortt sp $ Just a) (elmt sp $ Just m) of
        Just _  -> return $ PiExpr tv b
        Nothing -> do
            addErrorMsg $ lamMsg ex
            return Unknown

expr dr sp (AppExpr f c) = do
    f_type <- exprwh dr sp f
    exa    <- expr dr sp c
    case f_type of
        PiExpr tv@(TVar _ exa') b -> do
            a  <- return $ reduce_to_nf dr exa
            a' <- return $ reduce_to_nf dr exa'
            if not (equal a a')
                then do
                    addErrorMsg $ appMsg1 f f_type c a a'
                    return Unknown
                else return $ applySSubst (Sub tv c) b

        _                       -> do
            addErrorMsg $ appMsg2 f f_type c exa
            return Unknown

expr dr sp ce@(CaseExpr ex alts Unknown) = do
    ex_type                      <- expr dr sp ex
    _                            <- return $ leftMost ex_type
    atcas                        <- return $ ex_atcas ex_type
    rt <- forM alts $ \ (Alt _ tcas _ res') -> do
        subst <- return $ zipWith Sub tcas atcas 
        res   <- return $ applySubst subst res'
        expr dr sp res

    case foldr1 (\ t1 t2 -> if equal t1 t2 then t1 else Unknown) rt of
        Unknown -> do
            addErrorMsg $ caseMsg ce
            return Unknown
        ct      ->
            return ct

expr _ _ (CaseExpr _ _ t) = return t

expr _ _ (LitExpr lit) =
    case lit of
        LitInt _ -> return $ LitExpr IntType
        IntType  -> return $ SortExpr Star

expr _ _ Unknown = return Unknown


lookup' :: (Eq a, Eq b) => (a, b) -> [(a, b, c)] -> Maybe (a, b, c)
lookup' (a, b) l =
    case filter (\ (t1, t2, _) -> t1 == a && t2 == b) l of
        x : _ -> Just x
        _     -> Nothing


ex_atcas :: Expr -> [Expr]
ex_atcas =
    let ex_atcas' (AppExpr ex1 ex2) = ex_atcas' ex1 ++ [ex2]
        ex_atcas' ex = [ex]
    in tail . ex_atcas'


--------------------------------------------------------------------------------  
-- Fancy Error Messages
--------------------------------------------------------------------------------                             
appMsg1 :: Expr -> Expr -> Expr -> Expr -> Expr -> Error
appMsg1 f f_type a a_type var_type
 = "Type error in application   : " ++ expr2string (AppExpr f a) ++ "\n" ++
   "Left Expr                   : " ++ expr2string f             ++ "\n" ++
   "Type Left Expr              : " ++ expr2string f_type        ++ "\n" ++
   "Right Expr                  : " ++ expr2string a             ++ "\n" ++
   "Type Right Expr             : " ++ expr2string a_type        ++ "\n" ++
   "Type mismatch because       : " ++ expr2string a_type        ++ "\n" ++ 
   "does not match              : " ++ expr2string var_type      ++ "\n"


lamMsg :: Expr -> Error
lamMsg _ = "lamerror"


appMsg2 :: Expr -> Expr -> Expr -> Expr -> Error
appMsg2 ex1 ex1_type ex2 ex2_type 
 = "Type error in application   : " ++ expr2string (AppExpr ex1 ex2) ++ "\n" ++
   "Left Expr                   : " ++ expr2string ex1               ++ "\n" ++
   "Type Left Expr              : " ++ expr2string ex1_type          ++ "\n" ++
   "Right Expr                  : " ++ expr2string ex2               ++ "\n" ++
   "Type Right Expr             : " ++ expr2string ex2_type          ++ "\n" ++
   "Left expression does not have PI-type!!"                         ++ "\n"

bindMsg :: TVar -> Expr -> Expr -> Expr -> Error
bindMsg tv tv_type ex ex_type 
 = "Type error in binding       : " ++ tVar2string tv ++ " = " ++ expr2string ex  ++ "\n" ++
   "Variable                    : " ++ tVar2string tv                ++ "\n" ++
   "Type                        : " ++ expr2string tv_type           ++ "\n" ++
   "Expression                  : " ++ expr2string ex                ++ "\n" ++
   "Type Expression             : " ++ expr2string ex_type           ++ "\n"

noSortAMsg :: Expr -> Error
noSortAMsg piExpr@(PiExpr tv@(TVar _ a) _)
 = "Type error in Pi expression" ++ "\n" ++  
   "Pi expression               : " ++ expr2string piExpr            ++ "\n" ++
   "Variable                    : " ++ tVar2string tv                ++ "\n" ++
   "Type of variable            : " ++ expr2string a                 ++ "\n" ++
   "is not typable by a sort!"
noSortAMsg _ = undefined

noSortBMsg :: Expr -> Expr -> Error
noSortBMsg piExpr@(PiExpr (TVar _ _) b) btype
 = "Type error in Pi expression" ++ "\n" ++
   "Pi expression               : " ++ expr2string piExpr            ++ "\n" ++
   "Body                        : " ++ expr2string b                 ++ "\n" ++
   "Type of body reduces to     : " ++ expr2string btype             ++ "\n" ++
   "but should be a sort!"
noSortBMsg _ _ = undefined

ruleMsg :: Expr -> Sort -> Sort  -> Error
ruleMsg piExpr s1 s2
 = "Current type system is not strong enough!!\n" ++
   "One needs a rule of the form: (" ++ (expr2string $ SortExpr s1) ++ "," ++ (expr2string $ SortExpr s2) ++ ", _)" ++ "\n" ++
   "To type                     : " ++ expr2string piExpr  ++ "\n"

noAxiomMsg :: Sort -> Error
noAxiomMsg s1 = "There is no axiom to type sort: " ++ expr2string (SortExpr s1) ++ " !! \n"

caseMsg :: Expr -> Error
caseMsg ce = "Result expressions have different types in: " ++ expr2string ce

