module Main where
import Lex
import Parse
import Languages
import ModalSimplify
import FOLCorrespondent
import UniformFOLCorr
import Data.GraphViz.Types.Monadic
import Data.GraphViz.Commands
import GraphTest

main :: IO ()
main = do
    _ <- runGraphviz withDisjEq Jpeg "testgraph.jpeg"
    input <- getLine
    case parse (alexScanTokens input) of
        Left p -> error $ "error at " ++ show p
        Right f -> do
          print f
          -- case getPullDsFOL (toModBxA (modSimp f)) of
          --   f1 -> print f1
          case getSqBxA1 (toModBxA (modSimp f)) of
            Nothing -> do 
                putStrLn "Not Sahlqvist."
                (if isUniform (toModBxA (modSimp f)) then do
                  putStrLn "Uniform"
                  print (getFOLuniform (toModBxA (modSimp f)))
                  putStrLn (ppFOLForm (getFOLuniform (toModBxA (modSimp f))))
                else do
                  putStrLn "Not uniform."
                  -- computable combi cases do live here: e.g. (~[]<>p&(p->[]p))
                  )
            Just folF -> do
              putStrLn "Sahlqvist."
              (if isUniform (toModBxA (modSimp f)) then
                putStrLn "Uniform."
              else
                putStrLn "Not uniform.")
              print folF
              putStrLn (ppFOLForm folF)
              
              
-- ~(p&<><>p)->[]p      (~p|~<><>p)->[]p       (~p->[]p)&(~<><>p->[]p)     ([]p|p)&(<><>p|[]p)   ([]p&<><>p)|([]p)|(p&<><>p)|(p|[]p)
-- ([]p|<>(p&<>p)|~[]q)->p   ([]p|<>((p&<>p)|~q))->p