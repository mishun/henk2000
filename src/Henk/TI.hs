module Henk.TI
    ( timain
    , tiexpr
    ) where

import Control.Monad (mapAndUnzipM)
import Henk.AS
import Henk.PP (var2string)
import Henk.TermSupport (SSubst(..), applyStrongSubst)


type Annotation  = (Var, Expr)
type Annotations = [Annotation]
type Error       = String
type Errors      = [Error] 

tVar2Ann :: TVar -> Annotation
tVar2Ann (TVar v ex) = (v, ex)

--------------------------------------------------------------------------------  
-- The Type Inference Monad
-------------------------------------------------------------------------------- 
newtype TI t = TI (Annotations -> (Errors, t))

instance Monad TI where
    return x   = TI (\ _ -> ([], x))
    TI f >>= g = TI (\ ann -> let (erf, ta)       = f ann
                                  TI gta          = g ta
                                  (erg, tb)       = gta ann
                              in (erf ++ erg, tb))
                       
runTI        :: Annotations -> Program -> TI a -> (Errors, a)
runTI anns _ (TI f) = (er, result)
 where (er,result) = f anns

timain :: Annotations -> Program -> (Errors, (Program, Annotations))
timain anns p = runTI anns p (program p)

tiexpr :: Annotations -> Program -> Expr -> (Errors, Expr)
tiexpr anns p ex = runTI anns p (expr p ex)

addErrorMsg :: String -> TI ()
addErrorMsg s = TI (\ _ -> ([s], ()))

withAnn :: Annotation -> TI a -> TI a
withAnn ann (TI f) = TI (\ anns -> f (ann : anns))

withAnns :: Annotations -> TI a -> TI a
withAnns anns' (TI f) = TI (\ anns -> f (anns' ++ anns))

getAnn :: TI Annotations
getAnn = TI (\ ann -> ([], ann))

lookup' :: Var -> TI Expr
lookup' v = do
    ann <- getAnn
    case lookup v ann of 
        Just ex -> return ex
        Nothing -> do
            addErrorMsg $ "Warning: Could not derive type of bound variable: " ++ var2string v
            return Unknown

--------------------------------------------------------------------------------  
-- Program
--------------------------------------------------------------------------------
program :: Program -> TI (Program, Annotations)
program p@(Program tds0 vds0) = do
    (tds1, anns0) <- mapAndUnzipM (tDeclIdent p) tds0
    (tds, annss)  <- mapAndUnzipM (withAnns anns0 . tDeclBody p) tds1
    anns1         <- return $ concat annss ++ anns0
    (vds1, anns2) <- help p vds0 anns1
    anns3         <- return $ anns2 ++ anns1
    vds2          <- mapM (withAnns anns3 . vDeclBody p) vds1
    return (Program tds vds2, anns3)


help :: Program -> [VDecl] -> Annotations -> TI ([VDecl], Annotations)
help _ [] anns = return ([], anns)
help p (vd : vds) anns = do
    (vd', anns2) <- withAnns anns (vDeclIdent p vd)
    (vds', anns3) <- help p vds (anns ++ anns2)
    return (vd' : vds', anns3)

--------------------------------------------------------------------------------                     
-- Type Declarations
--------------------------------------------------------------------------------
tDeclIdent :: Program -> TDecl -> TI (TDecl, Annotation)
tDeclIdent p (TDecl tv tvs) = do
    tv' <- bindVar p tv
    return (TDecl tv' tvs, tVar2Ann tv')


tDeclBody :: Program -> TDecl -> TI (TDecl, Annotations)
tDeclBody p (TDecl tv tvs) = do
    tvs' <- mapM (bindVar p) tvs
    return (TDecl tv tvs', map tVar2Ann tvs')


--------------------------------------------------------------------------------
-- Value Declarations
--------------------------------------------------------------------------------

vDeclIdent :: Program -> VDecl -> TI (VDecl,Annotations)
vDeclIdent p (VDecl tv ex) = do
    tv' <- bindVar p tv
    return (VDecl tv' ex, [tVar2Ann tv'])


vDeclBody :: Program -> VDecl -> TI VDecl
vDeclBody p (VDecl tv ex) = do
    ex' <- expr p ex
    return $ VDecl tv ex'


bindVar :: Program -> TVar -> TI TVar
bindVar p (TVar v ex) =
    case ex of
        Unknown -> do
            addErrorMsg $ "Warning: Unannotated bind variable: " ++ var2string v
            return $ TVar v Unknown
        _       -> do
            ex' <- expr p ex
            return $ TVar v ex'


boundVar :: Program -> TVar -> TI TVar
boundVar p (TVar v ex) =
    case ex of
        Unknown -> do
            ex' <- lookup' v
            return $ TVar v ex'
        _       -> do
            ex' <- expr p ex
            return $ TVar v ex'


--------------------------------------------------------------------------------  
-- Expressions
--------------------------------------------------------------------------------                                                                                                             
expr :: Program -> Expr -> TI Expr
expr p (AppExpr ex1 ex2) = do
    ex1' <- expr p ex1
    ex2' <- expr p ex2
    return $ AppExpr ex1' ex2'

expr p (VarExpr tv) = do
    tv' <- boundVar p tv
    return $ VarExpr tv'

expr p (LamExpr tv ex) = do
    tv' <- bindVar p tv                                 
    ex' <- withAnn (tVar2Ann tv') (expr p ex)
    return $ LamExpr tv' ex'

expr p (PiExpr tv ex) = do
    tv' <- bindVar p tv
    ex' <- withAnn (tVar2Ann tv') (expr p ex)
    return $ PiExpr tv' ex'

expr p (CaseExpr ex as ct) =  do
    ex' <- expr p ex
    as' <- mapM (alt p) as
    ct' <- expr p ct  
    return $ CaseExpr ex' as' ct'

expr _ ex = return ex


alt :: Program -> Alt -> TI Alt
alt p (Alt dc tcas dcas res) = do
    dc'@(TVar _ dc_type) <- boundVar p dc
    as                   <- return $ tcas ++ dcas
    anns                 <- return $ map tVar2Ann $ match dc_type as
    res'                 <- withAnns anns (expr p res)
    return $ Alt dc' tcas dcas res'


match :: Expr -> [TVar] -> [TVar]
match (PiExpr ptv@(TVar _ t) ex) ((TVar v1 _) : vs) =
    let sub = applyStrongSubst [Sub ptv $ VarExpr (TVar v1 t)] ex
    in TVar v1 t : match ({- trace (expr2string sub) -} sub) vs
match _ _ = []

