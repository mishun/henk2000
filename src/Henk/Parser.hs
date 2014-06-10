module Henk.Parser
    ( program
    ) where

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Language
import Text.ParserCombinators.Parsec.Token
import Henk.AS


henk :: LanguageDef st
henk  = emptyDef
    { commentStart    = "{-"
    , commentEnd      = "-}"
    , commentLine     = "--"
    , nestedComments  = True
    , identStart      = letter
    , identLetter     = alphaNum <|> oneOf "_'"
    , opStart         = opLetter henk
    , opLetter        = oneOf ":=\\->/|~.*[]"
    , reservedOpNames = [ "::", "=", "\\", "->", "=>", "/\\", "\\/"
                        , "|~|", ".", ":", "*", "[]"
                        ]
    , reservedNames   = [ "case", "data", "letrec", "type"
                        , "import", "in", "let", "of", "at", "Int"
                        ]
    , caseSensitive   = True
    }


henkT :: TokenParser st
henkT = makeTokenParser henk


program :: Parser Program
program =  do
    whiteSpace henkT
    (tds, vds) <- manyAlternate typeDecl varDecl
    eof
    return $ Program tds vds


manyAlternate :: Parser a -> Parser b -> Parser ([a], [b])
manyAlternate pa pb = choice
    [ do
        as <- many1 pa
        (as', bs') <- manyAlternate pa pb
        return (as ++ as', bs')

    , do
        bs <- many1 pb
        (as', bs') <- manyAlternate pa pb
        return (as', bs ++ bs')

    , return ([], [])
    ]


typeDecl :: Parser TDecl
typeDecl = (<?> "type declaration") $ do
    reserved henkT "data"
    t <- bindVar
    _ <- symbol henkT "="
    ts <- braces henkT $ semiSep1 henkT bindVar 
    return $ TDecl t ts


varDecl :: Parser VDecl
varDecl  = (<?> "value declaration") $ do
    reserved henkT "let"
    tv <- parseVar Unknown (wildcard <|> var)
    _ <- symbol henkT "="
    ex <- expr
    return $ VDecl tv ex


expr :: Parser Expr
expr = (<?> "expression") $ choice
    [ (<?> "pi expression") $ do
        _ <- symbol henkT "|~|" <|> symbol henkT "∏" <|> symbol henkT "𝚷" <|> symbol henkT "\\/" <|> symbol henkT "∀"
        tvs <- sepBy1 bindVar (comma henkT)
        _ <- symbol henkT "."
        e <- expr
        return $ foldr PiExpr e tvs

    , (<?> "lambda expression") $ do
        _ <- symbol henkT "\\" <|> symbol henkT "/\\" <|> symbol henkT "λ" <|> symbol henkT "Λ"
        tvs <- commaSep1 henkT bindVar
        _ <- symbol henkT "."
        e <- expr
        return $ foldr LamExpr e tvs

    , (<?> "Case Expression") $ do
        reserved henkT "case"
        ex <- expr
        reserved henkT "of"

        as <- braces henkT $ semiSep1 henkT $
            (<?> "case alternative") $ do
                tc <- parseVar Unknown var
                tcas <- map (\ v -> TVar v Unknown) `fmap` many var
                _ <- symbol henkT "=>"
                res <- expr
                return $ Alt tc tcas [] res

        case_type <- option Unknown $ do
            reserved henkT ":"
            case_type <- expr
            return case_type

        return $ CaseExpr ex as case_type

    , let arrow = do
              _ <- symbol henkT "->"
              return $ \ ex1 ex2 -> PiExpr (TVar Anonymous ex1) ex2

          appExpr = (<?> "application") $ do
              atoms <- many1 atomExpr;
              return $  foldl1 AppExpr atoms

      in chainr1 appExpr arrow <?> "function expression"
    ]


atomExpr :: Parser Expr
atomExpr = (<?> "atomic expression") $ choice
    [ (<?> "variable expression") $ do
        tv <- parseVar Unknown var
        return $ VarExpr tv

    , (<?> "literal expression") $
        LitExpr `fmap` choice
            [ do
                i <- natural henkT
                return $ LitInt i

            , do
                reserved henkT "Int"
                return IntType
            ]

    , (<?> "sort expression") $
        SortExpr `fmap` choice
            [ try $ do
                _ <- symbol henkT "*"
                n <- natural henkT
                return $ SortNum n

            , do
                _ <- symbol henkT "*"
                return Star

            , do
                _ <- symbol henkT "||" <|> symbol henkT "□"
                return Box
            ]
{-
    , (<?> "list expression") $
        brackets henkT $ do
            elems <- expr `sepBy` comma henkT
            return $
                let nil = AppExpr (VarExpr (TVar (Var "Nil") Unknown)) Unknown
                    cons el = AppExpr (AppExpr (AppExpr (VarExpr (TVar (Var "Cons") Unknown)) Unknown) el)
                in foldr cons nil elems
-}
    , do
        _ <- symbol henkT "?"
        return Unknown

    , parens henkT expr
    ]


var :: Parser Var
var = do
    v <- identifier henkT
    return $ Var v


wildcard :: Parser Var
wildcard = do
    _ <- symbol henkT "_"
    _ <- option "" (identifier henkT)
    return Anonymous


parseVar :: Expr -> Parser Var -> Parser TVar
parseVar defType varP = (<?> "variable") $ do
    v <- varP
    t <- do { _ <- symbol henkT ":" ; expr } <|> return defType
    return $ TVar v t


bindVar :: Parser TVar
bindVar = parseVar (SortExpr Star) (wildcard <|> var)

