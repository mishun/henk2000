module Henk.AS
    ( Program(..)
    , TDecl(..)
    , VDecl(..)
    , TCons
    , DCons
    , Expr(..)
    , TVar(..)
    , Var(..)
    , Alt(..)
    , Lit(..)
    , Sort(..)
    ) where


data Program = Program [TDecl] [VDecl]
    deriving (Show)


data TDecl = TDecl TCons [DCons]
    deriving (Show)


type TCons = TVar  -- Type Constructor
type DCons = TVar  -- Data Constructor


data VDecl = VDecl TVar Expr
    deriving (Show)


data Expr
    = LamExpr TVar Expr
    | PiExpr TVar Expr
    | AppExpr Expr Expr
    | CaseExpr Expr [Alt] Expr
    | VarExpr TVar
    | LitExpr Lit
    | SortExpr Sort
    | Unknown
    deriving (Show, Eq)


data TVar = TVar Var Expr
    deriving (Show, Eq)


data Var
    = Var String
    | Anonymous
    deriving (Show, Eq)


data Alt
    = Alt TCons [TCA] [DCA] Expr
    deriving (Show, Eq)


type TCA = TVar -- type constructor argument
type DCA = TVar -- data constructor argument


data Lit
    = LitInt  Integer
    | IntType
    deriving (Show, Eq)


data Sort
    = Star
    | Box
    | SortNum Integer
    deriving (Show, Eq)
