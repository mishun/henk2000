module Henk.Classification
    ( functional
    , injective
    , rho
    , elmt
    , sortt
    ) where

import Data.List (find)
import Henk.AS
import Henk.TypeSystems (Specification)


crossproduct :: [a] -> [(a, a)]
crossproduct s = [(s1, s2) | s1 <- s, s2 <- s]


functional :: Specification -> Bool
functional (s, a, r) =
    and (map (\ s' -> length (filter (\ (s1, _) -> s1 == s') a) < 2) s) &&
    and (map (\ t -> length (filter (\ (s1, s2, _) -> (s1, s2) == t) r) < 2) (crossproduct s))


injective :: Specification -> Bool
injective (s, a, r) =
    functional (s, a, r) && 
        and (map (\ s' -> length (filter (\ (_, s2) -> s2 == s') a) < 2) s) &&
        and (map (\ t -> length (filter (\ (s1, _, s3) -> (s1, s3) == t) r) < 2) (crossproduct s))


minus :: Specification -> Maybe Sort -> Maybe Sort
minus (_, a, _) ms = do
    s <- ms
    (s', _) <- find ((== s) . snd) a
    return s'


plus :: Specification -> Maybe Sort -> Maybe Sort
plus (_, a, _) ms = do
    s <- ms
    (_, s') <- find ((== s) . fst) a
    return s'


rho :: Specification -> Maybe Sort -> Maybe Sort -> Maybe Sort
rho (_, _, r) ms1 ms2 = do
    s1 <- ms1
    s2 <- ms2
    (_, _, s3') <- find (\ (s1', s2', _) -> s1 == s1' && s2' == s2) r
    return s3'


mu :: Specification -> Maybe Sort -> Maybe Sort -> Maybe Sort
mu (_, _, r) ms1 ms2 = do
    s1 <- ms1
    s2 <- ms2
    (_, s3', _) <- find (\ (s1', _, s2') -> s1 == s1' && s2' == s2) r
    return s3'


elmt :: Specification -> Maybe Expr -> Maybe Sort
elmt sp me = do
    e <- me
    case e of
        VarExpr  (TVar _ e')   -> sortt sp $ Just e'
        SortExpr s             -> plus sp $ plus sp $ Just s
        AppExpr m n            -> mu sp (elmt sp $ Just n) (elmt sp $ Just m)
        LamExpr (TVar _ e1) e2 -> rho sp (sortt sp $ Just e1) (elmt sp $ Just e2)
        PiExpr _ _             -> plus sp $ sortt sp $ Just e
        LitExpr IntType        -> Just Star
        LitExpr _              -> Nothing
        CaseExpr _ alts _      -> let Alt _ _ _ res : _ = alts
                                  in elmt sp $ Just res
        Unknown                -> Nothing


sortt :: Specification -> Maybe Expr -> Maybe Sort
sortt sp me = do
    e <- me
    case e of
        VarExpr tv            -> minus sp $ elmt sp $ Just $ VarExpr tv
        SortExpr s            -> plus sp $ Just s
        AppExpr _ _           -> minus sp $ elmt sp $ Just e
        LamExpr _ _           -> minus sp $ elmt sp $ Just e
        PiExpr (TVar _ e1) e2 -> rho sp (sortt sp $ Just e1) (sortt sp $ Just e2)
        LitExpr (LitInt _)    -> Just Star
        LitExpr IntType       -> Just Box
        CaseExpr _ alts _     -> let Alt _ _ _ res : _ = alts
                                 in sortt sp $ Just res
        Unknown               -> Nothing

