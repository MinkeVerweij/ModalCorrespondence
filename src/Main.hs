module Main where
import Lex
import Parse
import Languages
import ModalSimplify
import FOLCorrespondent

main :: IO ()
main = do
    input <- getLine
    case parse (alexScanTokens input) of
        Left p -> error $ "error at " ++ show p
        Right f -> do
          print f
          -- case getPullDsFOL (toModBxA (modSimp f)) of
          --   f1 -> print f1
          case getSqBxA1 (toModBxA (modSimp f)) of
            Nothing -> putStrLn "Not Sahlqvist."
            Just folF -> do
              print folF
              putStrLn (ppFOLForm folF)
              
              
-- ~(p&<><>p)->[]p      (~p|~<><>p)->[]p       (~p->[]p)&(~<><>p->[]p)     ([]p|p)&(<><>p|[]p)   ([]p&<><>p)|([]p)|(p&<><>p)|(p|[]p)
-- ([]p|<>(p&<>p)|~[]q)->p   ([]p|<>((p&<>p)|~q))->p