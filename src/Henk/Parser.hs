module Henk.Parser
    ( program
    , single_expr
    ) where

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Language
import Text.ParserCombinators.Parsec.Token
import Henk.AS


henk :: LanguageDef st
henk  = emptyDef
		{ commentStart	  = "{-"
		, commentEnd	  = "-}"
		, commentLine	  = "--"
		, nestedComments  = True
		, identStart	  = letter
		, identLetter	  = alphaNum <|> oneOf "_'"
		, opStart         = opLetter henk
		, opLetter        = oneOf ":=\\->/|~.*[]"
		, reservedOpNames = ["::","=","\\","->","=>","/\\","\\/"
		                    ,"|~|",".",":","*","[]"]
		, reservedNames   = [ "case", "data", "letrec", "type"
				    , "import", "in", "let", "of", "at", "Int"
				    ]
                , caseSensitive  = True
		}


henkT :: TokenParser st
henkT = makeTokenParser henk


----------------------------------------------------------------
-- The Program
----------------------------------------------------------------
program :: Parser Program
program =  do{whiteSpace henkT
             ;(tds,vds) <- manyAlternate tDecl vDecl
             ;eof
             ;return $ Program tds vds
             }

manyAlternate :: Parser a -> Parser b -> Parser ([a],[b])
manyAlternate pa pb = do{as<-many1 pa; (as',bs') <- manyAlternate pa pb; return (as++as',bs')}
                      <|>
                      do{bs<-many1 pb; (as',bs') <- manyAlternate pa pb; return (as',bs++bs')}
                      <|> 
                      return ([],[])

----------------------------------------------------------------
-- Type Declaration
----------------------------------------------------------------
tDecl :: Parser TDecl
tDecl =  do{reserved henkT "data"
           ;t <- bindVar
           ;_ <- symbol henkT "="
           ;ts <- braces henkT $ semiSep1 henkT bindVar 
           ;return $ TDecl t ts
           }
           <?> "type declaration"
           
----------------------------------------------------------------
-- Value Declaration
----------------------------------------------------------------
vDecl :: Parser VDecl
vDecl  = letnonrec <?> "value Declaration"

letnonrec :: Parser VDecl
letnonrec  = do{reserved henkT "let"
               ;tv <- bindVar'
               ;_ <- symbol henkT "="
               ;ex <- expr
               ;return $ VDecl tv ex
               }
 

----------------------------------------------------------------
-- Expression
----------------------------------------------------------------
expr :: Parser Expr       
expr = choice
     [piExpr    --pi (\/) before lambda (\) to improve parser efficiency.
     ,lamExpr
     ,caseExpr   
     ,funExpr
     ]
     <?> "expression"


atomExpr :: Parser Expr
atomExpr =  choice
            [varExpr        
            ,litExpr
            ,sort
            ,unknown
            ,parens henkT expr
            ]
            <?> "atomic expression"

--single expression
single_expr :: Parser Expr
single_expr =do { whiteSpace henkT
                ; ex <- expr
                ; return ex
                }
             
----------------------------------------------------------------- 
-- Application
-----------------------------------------------------------------
appExpr :: Parser Expr
appExpr = do{atoms <- many1 atomExpr;
             return $  foldl1 AppExpr atoms}
          <?> "application"
               
----------------------------------------------------------------        
-- (Capital) Lambda Expression
----------------------------------------------------------------
lamExpr :: Parser Expr
lamExpr =  do{_ <- symbol henkT "\\" <|> symbol henkT "/\\" <|> symbol henkT "λ" <|> symbol henkT "Λ"
            ;tvs <- commaSep1 henkT bindVar
            ;_ <- symbol henkT "."
            ;e <- expr
            ;return $ foldr LamExpr e tvs}
            <?> "lambda expression"

----------------------------------------------------------------
-- Pi Expression / ForAll Expression
----------------------------------------------------------------
piExpr :: Parser Expr
piExpr  = do{ _ <- (symbol henkT "|~|" <|> symbol henkT "∏" <|> symbol henkT "𝚷") <|> (symbol henkT "\\/" <|> symbol henkT "∀")
          ;tvs <- sepBy1 bindVar (comma henkT)
          ;_ <- symbol henkT "."
          ;e <- expr 
          ;return $ foldr PiExpr e tvs}   
          <?> "pi expression"


---------------------------------------------------------------- 
-- Function Expression
---------------------------------------------------------------- 
funExpr :: Parser Expr
funExpr = chainr1 appExpr arrow <?> "function expression"
 where
 arrow = do{_ <- symbol henkT "->"
           ; return $ \ex1 ex2 -> PiExpr (TVar Anonymous ex1) ex2
           }
          
                         
            
---------------------------------------------------------------- 
-- Case Expression
---------------------------------------------------------------- 
caseExpr :: Parser Expr
caseExpr = do{reserved henkT "case"
             ;ex  <- expr
             ;reserved henkT "of"
             ;as  <- braces henkT $ semiSep1 henkT alt
             ;case_type <- option Unknown (do {reserved henkT ":"; case_type <- expr ; return case_type}) 
             ;return $ CaseExpr ex as case_type
             }
             <?> "Case Expression" 
  
alt :: Parser Alt
alt = do{tc   <- boundVar
        ;tcas' <- many var
	;tcas <- return $ map (\v -> TVar v Unknown) tcas'
        ;_ <- symbol henkT "=>"
        ;res <- expr
        ;return $ Alt tc tcas [] res
        }
        <?> "case alternative"
              
---------------------------------------------------------------- 
-- Variable Expression
---------------------------------------------------------------- 
varExpr :: Parser Expr
varExpr = do{tv <- boundVar
            ;return $ VarExpr tv
            }
            <?> "variable expression"

          
----------------------------------------------------------------
-- Variable
----------------------------------------------------------------
var :: Parser Var
var = do{v <- identifier henkT
        ;return $ Var v
        }

anonymousvar :: Parser Var
anonymousvar = 
      do{_ <- symbol henkT "_"
        ;v <- option "" (identifier henkT)
        ;return $ Var ('_':v)
        }

----------------------------------------------------------------
-- Binding Variable       
----------------------------------------------------------------
bindVar :: Parser TVar    
bindVar = do{v <- (anonymousvar <|> var)          
          ;(do {e <- isOfType 
               ; return $ TVar v e 
               }
            <|>
            (return $ TVar v (SortExpr Star)))      --  convention for binding variables 
          }
          <?> "variable"

bindVar' :: Parser TVar    
bindVar' = do{v <- (anonymousvar <|> var)          
             ;(do {e <- isOfType 
                  ; return $ TVar v e 
                  }
                  <|>
                 (return $ TVar v Unknown))      --  convention for lets 
             }
             <?> "variable"
         
isOfType :: Parser Expr
isOfType =  do{_ <- symbol henkT ":"
              ;aex <- expr
              ;return aex}
              
----------------------------------------------------------------
-- Bound Variable         
----------------------------------------------------------------
boundVar :: Parser TVar   
boundVar =  do{v <- var   
              ;(do {e <- isOfType 
                 ;return $ TVar v e 
                 }
                 <|>
              (return $ TVar v Unknown))      --  convention for bound variables 
              }
              <?> "variable"

----------------------------------------------------------------                  
-- Literal Expression
----------------------------------------------------------------
litExpr :: Parser Expr
litExpr = do {l <- lit 
             ;return $ LitExpr l
             }
             <?> "literal expression"
             
----------------------------------------------------------------
-- Literal
----------------------------------------------------------------
lit :: Parser Lit
lit = do{i <- natural henkT
        ;return $ LitInt i
        }                    
      <|>
      do{reserved henkT "Int"
        ;return $ IntType
        }                           

----------------------------------------------------------------
-- Sort
----------------------------------------------------------------
sort :: Parser Expr
sort = do{s <-    try (sortNum)
              <|> star
              <|> box
     ;return $ SortExpr s}   

sortNum :: Parser Sort
sortNum = do{ _ <- symbol henkT "*"
            ; n <- natural henkT
            ; return $ SortNum n
            }


star :: Parser Sort
star = do{ _ <- symbol henkT "*"
         ; return Star
         }


box  :: Parser Sort
box  = do{ _ <- symbol henkT "||" <|> symbol henkT "□"
         ; return Box
         } 

----------------------------------------------------------------
-- Unknown
----------------------------------------------------------------
unknown  :: Parser Expr
unknown  = do{ _ <- symbol henkT "?"
             ; return Unknown
             } 
