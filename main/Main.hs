---------------------------------------------------------------------
-- Henk 2000: Based on Pure Type Systems
-- by Jan-Willem Roorda
-- WWW: http://www.cs.uu.nl/~johanj/MSc/jwroorda
-- e-mail: jw@cs.uu.nl
---------------------------------------------------------------------

module Main (main) where

import System.Environment (getArgs)
import Text.ParserCombinators.Parsec (parseFromFile)
import Henk.Parser (program)
import Henk.PP (program2string)
import Henk.Int (intmain, prog2DeltaRules)
import Henk.TI (timain)
import Henk.TC (tcmain)
import Henk.TypeSystems (Specification, cc)


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
main = do
    putStr welcome

    (prelude_rules, prelude_anns) <- do
            putStrLn "Loading prelude.henk..."

            preludeAS <- do
                prelude_result <- parseFromFile program "prelude.henk"
                case prelude_result of
                    Right prog -> return prog
                    Left  err  -> do
                        print err
                        return $ error ""

            let prelude_rules = prog2DeltaRules preludeAS
            putStrLn "Type inferencing prelude.henk..."
            let (prelude_ti_er, (prelude_prog, prelude_anns)) = timain [] preludeAS
            putErrors prelude_ti_er
            putStrLn "Type checking prelude.henk..."
            let (prelude_tc_er, _) = tcmain prelude_rules typeSystem prelude_prog
            putErrors prelude_tc_er
            return (prelude_rules, prelude_anns)

    [fnprog] <- getArgs

    (prog_rules, prog) <- do
            putStrLn $ "Parsing " ++ fnprog ++ "..."

            progAS <- do
                prog <- parseFromFile program fnprog
                case prog of
                    Right d  -> return d
                    Left err -> do
                        print err
                        return $ error ""

            let prog_rules = prog2DeltaRules progAS
            putStrLn "Type inferencing..."
            let (er, (prog, _)) = timain prelude_anns progAS
            putErrors er
            putStrLn "Type checking..."
            let (er', _) = tcmain (prog_rules ++ prelude_rules) typeSystem prog
            putErrors er'
            return (prog_rules, prog)


    putStrLn $ program2string prog
    _ <- intmain (prog_rules ++ prelude_rules) prog
    putStrLn ""


putErrors :: [String] -> IO ()
putErrors xs = do
    mapM_ putStrLn (take 1 xs)
    putStrLn $ "Numbers of errors: " ++ show (length xs)

