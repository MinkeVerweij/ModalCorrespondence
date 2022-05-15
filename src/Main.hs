module Main where


import Lex
import Parse

import ModalSimplify
import FOLCorrespondent



main :: IO ()
main = do
    input <- getLine
    case parse (alexScanTokens input) of
        Left p -> error $ "error at " ++ show p
        Right f -> printMaybe (getSqBxA1 (toModBxA (modSimp f)))

-- [](p-><>p)
-- <>([]p|<><>p)->p 
-- [][](<>p->p)|(<><>q->q)
-- [][]([][](<>p->p)|(<><>q->q))
-- [][]((p&q)|(<>p|<>q)->([]p&q))
-- (p&<>~p)-><>p
-- [][][][][][][][][][](<>p->p)
-- ~[][]p
-- []((<>p|<><>p)->p)

printMaybe :: Show a => Maybe a -> IO ()
printMaybe m = case m of
  Nothing -> putStrLn "Not Sahlqvist"
  Just x -> print x