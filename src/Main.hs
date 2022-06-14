module Main where
import Lex
import Parse
import Languages
import ModalSimplify
import FOLCorrespondent
-- import Data.GraphViz.Types.Monadic
import Data.GraphViz.Commands
import GraphTest
import SahlqvistCheck
import MakeViz

main :: IO ()
main = do
    _ <- runGraphviz example Jpeg "testgraph.jpeg"
    input <- getLine
    case parse (alexScanTokens input) of
        Left p -> error $ "error at " ++ show p
        Right f -> do
          print f
          print (toModBxA (modSimp f))
          case getSqBxA1 (toModBxA (modSimp f)) of
            Nothing -> do 
              putStrLn "Not Sahlqvist. Not uniform. No Correspondent found."
            Just folF -> do
              (if isSqBxA (toModBxA (modSimp f)) then
                  putStrLn "Sahlqvist."
              else putStrLn "Not Sahlqvist")
              (if isUniform (toModBxA (modSimp f)) then
                  putStrLn "Uniform."
              else putStrLn "Not uniform.")
              print folF
              _ <- runGraphviz (toGraph (toClusters3 folF)) Jpeg "FOLCorrVis.jpeg"
              putStrLn (ppFOLForm folF)
              
              
-- ~(p&<><>p)->[]p      (~p|~<><>p)->[]p       (~p->[]p)&(~<><>p->[]p)     ([]p|p)&(<><>p|[]p)   ([]p&<><>p)|([]p)|(p&<><>p)|(p|[]p)
-- ([]p|<>(p&<>p)|~[]q)->p   ([]p|<>((p&<>p)|~q))->p