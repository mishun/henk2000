---------------------------------------------------------------------
-- Henk 2000: Based on Pure Type Systems
-- by Jan-Willem Roorda
-- WWW: http://www.cs.uu.nl/~johanj/MSc/jwroorda
-- e-mail: jw@cs.uu.nl
---------------------------------------------------------------------

module Main (main) where

import Text.ParserCombinators.Parsec (parseFromFile, parse)
import HenkParser (program, single_expr)
import HenkPP (program2string, expr2string)
import HenkInt (intmain, prog2DeltaRules)
import HenkTI (timain, tiexpr)
import HenkTC (tcmain, tcexpr)
import TypeSystems (Specification, cc)


welcome :: String
welcome = "__   __ ______ __  __ __      ______________________________________________\n"++
          "||   || ||_ || ||  || ||/     Henk 2000: Based on Pure Type Systems     \n"++
          "||___|| ||- __ ||\\ || ||\\                                               \n"++
          "||---|| ||__|| || \\|| 2000    WWW: http://www.cs.uu.nl/~johanj/MSc/jwroorda\n"++
          "||   ||                       Report bugs to: jw@cs.uu.nl                \n"++
          "||   ||                       ______________________________________________\n\n"


typeSystem :: Specification
typeSystem = cc


main :: IO ()
main = do{ putStr welcome
         ; putStr "Loading prelude.henk...\n\n"
         ; prelude_result <- parseFromFile HenkParser.program "prelude.henk"
         ; prelude_prog   <- case prelude_result of           
                               Left  err   -> do{putStr (show(err)); return $ error ""}             
                               Right prog  -> return prog             
         ; prelude_rules  <- return $ prog2DeltaRules prelude_prog
         ; putStr $ "Type inferencing prelude.henk...\n"
         ; (prelude_ti_er,(prelude_prog,prelude_anns))  <- return $ timain [] prelude_prog
         ; putErrors prelude_ti_er ; putStr "\n"
         ; putStr $ "Type checking prelude.henk...\n"
         ; (prelude_tc_er,_) <- return $ tcmain prelude_rules typeSystem prelude_prog
         ; putErrors prelude_tc_er
         ; putStr   "\nEnter name of programfile <prog.henk>:"
         ; fnprog   <- getLine
         ; fnprog   <- if fnprog=="" then return "prog.henk" else return $ fnprog
         ; putStr   $ "\nParsing "++fnprog++"...\n\n"
         ; prog     <- parseFromFile HenkParser.program fnprog   
         ; prog     <- case prog of           
                        Left err -> do{ putStr (show(err)); return $ error ""}             
                        Right d  -> return d
         ; putStrLn $ program2string prog
         ; prog_rules  <- return $ prog2DeltaRules prog              
         ; putStr $ "Type inferencing...\n"
         ; (er,(prog,_)) <- return $ timain prelude_anns prog    
         ; putErrors er         
         ; putStr "\n"
         ; putStr $ "Type checking...\n"
         ; (er,_) <- return $ tcmain (prog_rules++prelude_rules) typeSystem prog
         ; putErrors er
         ; ev_expr  <- (HenkInt.intmain (prog_rules++prelude_rules) prog)
         ; putStr   $ ""
         } 


putErrors :: [String] -> IO ()
putErrors xs = do {mapM_ (\s -> putStr $ s ++ "\n") (take 1 xs)
                  ;putStr $ "Numbers of errors: "++(show (length xs))++"\n"
                  ;return ()}


add_line_numbers :: String -> String
add_line_numbers s  =  (concat.(map (\(x,y) -> x++y)).(zip $ numbers l).(map (++"\n" ))) (lines s)
                       where     
                       l = length (lines s)


numbers :: Int -> [String]
numbers l = [ (zeros i) ++ (show i) ++ ": " | i <- [1 :: Int ..]]
            where
            zeros i = take (length (show l) - (length (show i))) ['0' | _ <- [0 :: Int ..]]


-- ti performs type inference on a single expression
ti :: String -> IO ()
ti s = 
       do{ putStr "Parsing expression....\n"
         ; mex <- return $ parse single_expr "" s 
         ; ex  <- case mex of 
                Left  err -> do{putStr (show(err)); return $ error ""}
                Right ex  -> return ex
         ; putStr "Loading prelude.henk...\n\n"
         ; prelude_result <- parseFromFile HenkParser.program "prelude.henk"
         ; prelude_prog   <- case prelude_result of           
                               Left  err   -> do{putStr (show(err)); return $ error ""}             
                               Right prog  -> return prog             
         ; prelude_rules  <- return $ prog2DeltaRules prelude_prog
         ; putStr $ "Type inferencing prelude.henk...\n"
         ; (prelude_ti_er,(prelude_prog,prelude_anns))  <- return $ timain [] prelude_prog
         ; putErrors prelude_ti_er ; putStr "\n"
         ; putStr $ "Type checking prelude.henk...\n"
         ; (prelude_tc_er,_) <- return $ tcmain prelude_rules typeSystem prelude_prog
         ; putErrors prelude_tc_er
         ; putStr   "\nEnter name of programfile <prog.henk>:"
         ; fnprog   <- return "" --getLine
         ; fnprog   <- if fnprog=="" then return "prog.henk" else return $ fnprog
         ; putStr   $ "\nParsing "++fnprog++"...\n\n"
         ; prog     <- parseFromFile HenkParser.program fnprog   
         ; prog     <- case prog of           
                        Left err -> do{ putStr (show(err)); return $ error ""}             
                        Right d  -> return d
         ; prog_rules  <- return $ prog2DeltaRules prog              
         ; putStr $ "Type inferencing program...\n"
         ; (er,(prog,prog_anns)) <- return $ timain prelude_anns prog    
         ; putErrors er         
         ; putStr "\n"
         ; putStr $ "Type checking program...\n"
         ; (er,_) <- return $ tcmain (prog_rules++prelude_rules) typeSystem prog
         ; putErrors er
         ; putStr "\n"
         ; putStr $ "Type inferencing expression...\n"
         ; (er,ex) <- return $ tiexpr (prelude_anns ++ prog_anns) prog ex
         ; putErrors er
         ; putStr "\n"
         ; putStr $ "Type checking expression...\n"
         ; (er,ext) <- return $ tcexpr (prog_rules++prelude_rules) typeSystem ex 
         ; putErrors er
         ; putStr "\n"
         ; putStr $ (expr2string ex) ++ " has type: " ++(expr2string ext)
         }
