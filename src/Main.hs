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
        Right f -> print (getFOLcorr (toModBxA (modSimp f)))