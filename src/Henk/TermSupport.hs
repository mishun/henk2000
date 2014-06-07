module Henk.TermSupport
    ( DeltaRule(..)
    , DeltaRules
    , RedexInf(..)
    , isRedex
    , lookup''
    , hnf
    , whnf
    , SSubst(..)
    , SubstC(..)
    , leftMost
    , applySubToLeftMost
    , applySStrongSubst
    , applyStrongSubst
    , equal
    ) where

import Henk.AS

--------------------------------------------------------------------------------  
-- Rules
--------------------------------------------------------------------------------
data DeltaRule       = DeltaRule TVar Expr
 deriving (Show,Eq)
type DeltaRules      = [DeltaRule] 


--------------------------------------------------------------------------------
-- Investigating the Redex Structure
--------------------------------------------------------------------------------
data RedexInf = NoRedex
              | BetaRedex
              | CaseRedex
              | DeltaRedex DeltaRule
 deriving (Show, Eq)

 
isRedex :: DeltaRules -> Expr -> RedexInf
isRedex _ (AppExpr (LamExpr _ _) _) = BetaRedex
isRedex _ (CaseExpr _ _ _)          = CaseRedex
isRedex deltaRules (VarExpr tv) =
    case lookup'' tv deltaRules of
        Just deltarule -> DeltaRedex deltarule
        Nothing        -> NoRedex
isRedex _ _ = NoRedex


lookup'' :: TVar -> DeltaRules -> Maybe DeltaRule
lookup'' tv@(TVar (Var v) _) (r@(DeltaRule ex1 _):rs) =
 case ex1 of
  (TVar (Var v1) _) | (v1==v)   -> Just r
                    | otherwise -> lookup'' tv rs
  _                             -> undefined
lookup'' _ _ = Nothing 


hnf :: DeltaRules -> Expr -> Bool 
hnf deltaRules expr = case expr of
  LamExpr _ ex1   -> hnf deltaRules ex1 
  AppExpr _  _    -> not $ or (map (\ex -> (isRedex deltaRules ex)/=NoRedex) [leftMostApp expr,leftMost expr])
  _               -> isRedex deltaRules expr == NoRedex


whnf :: DeltaRules -> Expr -> Bool
whnf deltaRules expr = case expr of
  LamExpr _  _    -> True
  AppExpr _  _    -> not $ or (map (\ex -> (isRedex deltaRules ex)/=NoRedex) [leftMostApp expr, leftMost expr])
  _               -> isRedex deltaRules expr == NoRedex

--------------------------------------------------------------------------------
-- Extracting Sub Expressions 
--------------------------------------------------------------------------------
leftMost :: Expr -> Expr
leftMost expr = case expr of
 (AppExpr ex1 _) -> leftMost ex1
 _               -> expr

leftMostApp :: Expr -> Expr
leftMostApp expr = case expr of
 (AppExpr ex1 _) -> case ex1 of
                       (AppExpr _ _) -> leftMostApp ex1
                       _             -> expr
 _               -> error "leftMostApp"


--------------------------------------------------------------------------------
-- (Weak) Substitutions
--------------------------------------------------------------------------------
-- weak substitution can only be used when there is not risk of
-- variable capturing

data SSubst         = Sub TVar Expr -- singleton substitution
     deriving Show
type Subst          = [SSubst]

class SubstC t where
  applySSubst  :: SSubst -> t -> t
  applySubst   :: Subst  -> t -> t
  -- default 
  applySubst subst expr  = foldr applySSubst expr subst   

instance SubstC Expr where
 applySSubst ssubst@(Sub (TVar vars _) exprs) expr = case expr of
  AppExpr exa exb                                 -> AppExpr (applySSubst ssubst exa) (applySSubst ssubst exb)
  LamExpr tv@(TVar var expr1) expr2 | (var==vars) -> LamExpr tv expr2
                                    | otherwise   -> LamExpr (TVar var (applySSubst ssubst expr1)) (applySSubst ssubst expr2)
  PiExpr  tv@(TVar var expr1) expr2 | (var==vars) -> PiExpr  tv expr2
                                    | otherwise   -> PiExpr  (TVar var (applySSubst ssubst expr1)) (applySSubst ssubst expr2)                          
  VarExpr (TVar var expr1)      | (var==vars)     -> exprs
                                | otherwise       -> VarExpr (TVar var (applySSubst ssubst expr1)) 
  CaseExpr expr1 alts t                           -> CaseExpr (applySSubst ssubst expr1) (applySSubst ssubst alts) (applySSubst ssubst t)                              
  exrest                                          -> exrest

instance SubstC Alt where
 applySSubst ssubst (Alt tc tcas dcas res) = Alt tc tcas dcas (applySSubst ssubst res) 

instance SubstC t => SubstC [t] where
 applySSubst ssubst xs = map (applySSubst ssubst) xs  
 

applySubToLeftMost :: Subst -> Expr -> Expr
applySubToLeftMost sub expr = case expr of
 (AppExpr ex1 ex2) -> AppExpr (applySubToLeftMost sub ex1) ex2 
 _                 -> applySubst sub expr


---------------------------------------------------------------------------------
-- Strong Substitions
---------------------------------------------------------------------------------
-- strong substitution is slower than weak substitution, but prevents 
-- capturing of variables by means of alpha conversion.
-- caution: very naive and slow implemenation!!!

class StrongSubstC t where
    applySStrongSubst  :: SSubst -> t -> t
    applyStrongSubst   :: Subst  -> t -> t
    -- default 
    applyStrongSubst subst expr  = foldr applySStrongSubst expr subst   

instance StrongSubstC Expr where
    applySStrongSubst ssubst@(Sub (TVar vars _) exprs) expr = case expr of
        AppExpr exa exb                                 -> AppExpr (applySStrongSubst ssubst exa) (applySStrongSubst ssubst exb)
        LamExpr tv ex                                   -> lamSStrongSubst ssubst (LamExpr tv ex) 
        PiExpr  tv ex                                   -> piSStrongSubst ssubst (PiExpr tv ex)                            
        VarExpr (TVar var expr1)      | var == vars     -> exprs
                                      | otherwise       -> VarExpr (TVar var (applySStrongSubst ssubst expr1)) 
        CaseExpr expr1 alts t                           -> CaseExpr (applySStrongSubst ssubst expr1) (applySStrongSubst ssubst alts) (applySStrongSubst ssubst t)                            
        exrest                                          -> exrest


freshFreeVars :: [Var]
freshFreeVars = [Var $ "v" ++ show i | i <- [1 :: Int ..]]

lamSStrongSubst :: SSubst -> Expr -> Expr
lamSStrongSubst ssubst@(Sub (TVar vars _) exprs) (LamExpr tv@(TVar var expr1) expr2) 
 | var==vars                            = LamExpr (TVar var (applySStrongSubst ssubst expr1)) expr2
 | not $ vars `elem` freeVarsExpr2      = LamExpr (TVar var (applySStrongSubst ssubst expr1)) expr2
 | not $ var  `elem` freeVarsExprs      = LamExpr (TVar var (applySStrongSubst ssubst expr1)) (applySStrongSubst ssubst expr2)
 | otherwise                            = lamSStrongSubst 
                                           ssubst 
                                           (LamExpr (TVar freshFreeVar expr1) 
                                            ((applySStrongSubst (Sub tv (VarExpr (TVar freshFreeVar expr1)))) expr2))  
 where
  freeVarsExprs = (exFreeVars exprs)
  freeVarsExpr2 = (exFreeVars expr2)
  freeVars      = freeVarsExprs ++ freeVarsExpr2
  freshFreeVar  = head(filter (\v->not(v `elem` freeVars)) freshFreeVars) 
lamSStrongSubst _ _ = undefined

piSStrongSubst :: SSubst -> Expr -> Expr
piSStrongSubst ssubst@(Sub (TVar vars _) exprs) (PiExpr tv@(TVar var expr1) expr2) 
    | var==vars                            = PiExpr (TVar var (applySStrongSubst ssubst expr1)) expr2
    | not $ vars `elem` freeVarsExpr2      = PiExpr (TVar var (applySStrongSubst ssubst expr1)) expr2
    | not $ var  `elem` freeVarsExprs      = PiExpr (TVar var (applySStrongSubst ssubst expr1)) (applySStrongSubst ssubst expr2)
    | otherwise                            = 
        piSStrongSubst ssubst 
                       (PiExpr (TVar freshFreeVar expr1) 
                       ((applySStrongSubst (Sub tv (VarExpr (TVar freshFreeVar expr1)))) expr2))  
    where
        freeVarsExprs = (exFreeVars exprs)
        freeVarsExpr2 = (exFreeVars expr2)
        freeVars      = freeVarsExprs ++ freeVarsExpr2
        freshFreeVar  = head(filter (\v->not(v `elem` freeVars)) freshFreeVars)

piSStrongSubst _ _ = undefined


instance StrongSubstC Alt where
 applySStrongSubst ssubst (Alt tc tcas dcas res) = Alt tc tcas dcas (applySStrongSubst ssubst res) 

instance StrongSubstC t => StrongSubstC [t] where
 applySStrongSubst ssubst xs = map (applySStrongSubst ssubst) xs


---------------------------------------------------------------------------------
-- Equality modulo alpha conversion
---------------------------------------------------------------------------------

equal :: Expr -> Expr -> Bool
equal (AppExpr ex1l ex1r)
      (AppExpr ex2l ex2r)                     = equal ex1l ex2l && equal ex1r ex2r
equal (LamExpr tv1@(TVar (Var v1) _) ex1)
      (LamExpr tv2@(TVar (Var v2) _) ex2)  = case (v1==v2) of
                                                True   -> equal ex1 ex2
                                                False  -> equal ex1 $ applySubst [Sub tv2 (VarExpr tv1)] ex2
equal (LamExpr (TVar Anonymous _) ex1)
      (LamExpr (TVar (Var _) _) ex2)       = equal ex1 ex2
equal (LamExpr (TVar (Var _) _) ex1)
      (LamExpr (TVar Anonymous _) ex2)     = equal ex1 ex2
equal (LamExpr (TVar Anonymous _) ex1)
      (LamExpr (TVar Anonymous _) ex2)     = equal ex1 ex2


equal (PiExpr tv1@(TVar (Var v1) _) ex1)
      (PiExpr tv2@(TVar (Var v2) _) ex2)  = case v1 == v2 of
                                                True   -> equal ex1 ex2
                                                False  -> equal ex1 $ applySubst [Sub tv2 (VarExpr tv1)] ex2
equal (PiExpr (TVar Anonymous _) ex1)
      (PiExpr (TVar (Var _) _) ex2)      = equal ex1 ex2
equal (PiExpr (TVar (Var _) _) ex1)
      (PiExpr (TVar Anonymous _) ex2)     = equal ex1 ex2
equal (PiExpr (TVar Anonymous _) ex1)
      (PiExpr (TVar Anonymous _) ex2)     = equal ex1 ex2


equal (VarExpr (TVar var1 _))
      (VarExpr (TVar var2 _))                 = var1==var2
equal (SortExpr s1) (SortExpr s2)             = s1 == s2
equal Unknown Unknown                         = True
equal (LitExpr l1) (LitExpr l2)               = l1 == l2
equal _ _                                     = False
                                           


---------------------------------------------------------------------------------
-- Free Variables
---------------------------------------------------------------------------------

class FreeVars t
  where exFreeVars :: t -> [Var]
 
instance FreeVars Expr where
    exFreeVars expr = case expr of
        AppExpr exa exb                                 -> exFreeVars exa ++ exFreeVars exb
        LamExpr (TVar var expr1) expr2                  -> filter (/=var) $ exFreeVars expr1 ++ exFreeVars expr2
        PiExpr  (TVar var expr1) expr2                  -> filter (/=var) $ exFreeVars expr1 ++ exFreeVars expr2
        VarExpr (TVar var expr1)                        -> var : exFreeVars expr1
        CaseExpr expr1 alts t                           -> exFreeVars expr1 ++ exFreeVars alts ++ exFreeVars t
        LitExpr _                                       -> []
        SortExpr _                                      -> []
        Unknown                                         -> []

instance FreeVars Alt where
    exFreeVars (Alt _ _ _ res) = exFreeVars res
 

instance FreeVars t => FreeVars [t] where
    exFreeVars xs = concat $ map exFreeVars xs

