module Main where
import Lex
import Parse
import Languages
import ModalSimplify
import FOLCorrespondent
import Data.GraphViz.Commands
import SahlqvistCheck
import MakeViz
import FOLSimplify

main :: IO ()
main = do
    input <- getLine
    case parse (alexScanTokens input) of
        Left p -> error $ "error at " ++ show p
        Right f -> do
          putStrLn ("Input: " ++ ppModForm f) -- confirm input

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

              -- compute + show FO Correspondent
              (if simpFOLViz2 folF == Topc then do
                _ <- runGraphviz topViz Pdf "FOLCorrVis.pdf"
                putStrLn ("First-Order Correspondent: " ++ ppFOLForm (simpFOLViz2 folF))
              else (if simpFOLViz2 folF == Negc Topc then do
                      _ <- runGraphviz botViz Pdf "FOLCorrVis.pdf"
                      putStrLn ("First-Order Correspondent: " ++ ppFOLForm (simpFOLViz2 folF))
                    else do
                      putStrLn ("First-Order Correspondent: " ++ ppFOLForm folF)
                      (if clusterDepth (simpFOLViz2 folF) 0 < 3 then -- visualization: not too much nesting
                        (if not (impliedOrs (simpFOLViz2 folF)) then do -- visualization: not too many implied ors (3 colors)
                          _ <- runGraphviz (toGraph (toClusters3 (simpFOLViz2 folF))) Pdf "FOLCorrVis.pdf"
                          -- _ <- runGraphviz (toGraph (toClusters3 (simpFOLViz2 folF))) Jpeg "FOLCorrVis.jpeg" -- to see in VSCode
                          putStrLn ("Formula simplified for visualisation: " ++ ppFOLForm (simpFOLViz2 folF))
                        else do
                          putStrLn "Cannot visualize this formula, too many implied disjuncts."
                          putStrLn ("Formula simplified for visualisation: " ++ ppFOLForm (simpFOLViz2 folF))
                        )
                        else do
                          putStrLn "Cannot visualize this formula, too many subclusters."
                          putStrLn ("Formula simplified for visualisation: " ++ ppFOLForm (simpFOLViz2 folF))
                        )
                    )
                )
