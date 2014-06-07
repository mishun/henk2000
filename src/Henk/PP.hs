module Henk.PP
    ( program2string
    , expr2string
    , var2string
    , tVar2string
    ) where

import Data.Maybe (isJust)
import Text.PrettyPrint
import Henk.AS


program2string :: Program -> String
program2string = render . program

expr2string :: Expr -> String
expr2string = render . expr

var2string :: Var -> String
var2string = render . var

tVar2string :: TVar -> String
tVar2string = render . boundVar

-- just for testing
--rules2string :: Rules -> String
--rules2string rs = concat $ map (\r -> (rule2string r)++"\n") rs
--rule2string :: Rule -> String
--rule2string (Rule ex1 ex2) = (expr2string ex1) ++ " --> "  ++ (expr2string ex2)  
 
----------------------------------------------------------------
-- The Program
----------------------------------------------------------------
program :: Program -> Doc
program (Program tds vds) =    vsep (map tDecl tds)
                            $$ vsep (map vDecl vds)

----------------------------------------------------------------
-- Type Declaration
----------------------------------------------------------------
tDecl :: TDecl -> Doc
tDecl (TDecl tv tvs) =     text "data"
                       <+> bindVar tv
                       $$  indent (    text "="
                                   <+> br_list (map bindVar tvs))

----------------------------------------------------------------
-- Value Declaration
----------------------------------------------------------------
vDecl :: VDecl -> Doc
vDecl (VDecl tv ex) = sep [bindVar tv, text "=" <+> expr ex]

----------------------------------------------------------------
-- Expression
----------------------------------------------------------------
expr :: Expr -> Doc

expr (LamExpr (TVar (Var v) (SortExpr Star)) ex1) = sep [text "Λ" <> text v <> text ".", expr ex1]
expr (LamExpr tv ex1)                             = sep [text "λ" <> bindVar tv <> text ".", expr ex1]
expr (PiExpr (TVar Anonymous ex1) ex2)            = sep [left_parents_function ex1 (expr ex1), text "->", (expr ex2)]
expr (PiExpr (TVar (Var v) (SortExpr Star)) ex2)  = sep [text "∀" <> text v <> text ".", expr ex2]
expr (PiExpr tv ex1)                              = sep [text "∏" <> bindVar tv <> text ".", expr ex1]

expr ex@(AppExpr ex1 ex2)                         =
    case tryListLiteral ex of
        Nothing      -> left_parents ex1 (expr ex1) <+> right_parents ex2 (expr ex2)
        Just []      -> text "[]"
        Just (h : t) -> text "[" <> expr h <> foldr (\ a b -> text ", " <> expr a <> b) (text "") t <> text "]"

expr (CaseExpr ex1 as _)                          = text "case" <+> expr ex1 <+> text "of" <+> indent (br_list (map alt as)) -- $$  text ":" <+> expr ex
expr (VarExpr tv)                                 = boundVar tv

expr (LitExpr l)                                  =
    case l of
        LitInt i -> text $ show i
        IntType  -> text "Int"

expr (SortExpr s)                                 =
    case s of
        Star      -> text "*"
        Box       -> text "□"
        SortNum i -> text $ "*" ++ show i

expr Unknown                                      = text "?"


right_parents :: Expr -> Doc -> Doc
right_parents ex d =
    case ex of
        AppExpr _ _ -> if isList ex then d else parens d
        LamExpr _ _ -> parens d
        PiExpr  _ _ -> parens d
        _           -> d


left_parents :: Expr -> Doc -> Doc
left_parents ex d =
    case ex of
        LamExpr _ _ -> parens d
        PiExpr  _ _ -> parens d
        _           -> d


left_parents_function :: Expr -> Doc -> Doc
left_parents_function ex d =
    case ex of
        PiExpr (TVar Anonymous _) _ -> parens d
        _                           -> d


alt :: Alt -> Doc
alt (Alt tc tcas dcas ex) =
                         boundVar tc
                     <+> (if null tcas then empty else comma_sep (map boundVar tcas))
                     <+> (if null dcas then empty else comma_sep (map boundVar dcas))
                     <+> text "=>"
                     <+> expr ex                                              

----------------------------------------------------------------
-- Variable
----------------------------------------------------------------
bindVar :: TVar ->  Doc
bindVar tv = case tv of 
 TVar (Var v) (SortExpr Star)          -> text v                         -- un-annotated binding variables have type star    
 TVar (Anonymous) (SortExpr Star)      -> text "_" 
 TVar (Var v) e                        -> text v   <> text ":" <> expr e 
 TVar (Anonymous) e                    -> text "_" <> text ":" <> expr e
                          
boundVar :: TVar ->  Doc
boundVar tv = case tv of
   TVar v Unknown         -> var v -- <> text ": ? "                     -- the type of un-annotated bound variables should be derived from the context
   TVar v _               -> var v -- <> text ":" <> expr e


var :: Var -> Doc
var (Var n)   = text n
var Anonymous = text "_"


----------------------------------------------------------------
-- Lists
----------------------------------------------------------------

tryListLiteral :: Expr -> Maybe [Expr]
tryListLiteral (AppExpr (VarExpr (TVar (Var "Nil") _ )) _) = Just []
tryListLiteral (AppExpr (AppExpr ( AppExpr (VarExpr (TVar (Var "Cons") _)) _) el) rest) = (el :) `fmap` tryListLiteral rest
tryListLiteral _ = Nothing


isList :: Expr -> Bool
isList = isJust . tryListLiteral


----------------------------------------------------------------
-- help functions
----------------------------------------------------------------
indent :: Doc -> Doc
indent = nest 2

vsep :: [Doc] -> Doc
vsep xs  = vcat (map ($$ text "") xs)

br_list :: [Doc] -> Doc
br_list (x:xs) = sep $    [text "{" <+> x] 
                       ++ foldr (\x' y -> [text ";" <+> x'] ++ y) [] xs
                       ++ [text "}"]
br_list []     = text "{}"

comma_sep :: [Doc] -> Doc 
comma_sep (x : xs) = x <> foldr (\ x' y -> text "," <+> x' <> y) empty xs
comma_sep [] = undefined

