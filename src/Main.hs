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
    -- _ <- runGraphviz example Jpeg "testgraph.jpeg"
    input <- getLine
    case parse (alexScanTokens input) of
        Left p -> error $ "error at " ++ show p
        Right f -> do
          putStrLn ("Input: " ++ ppModForm f)
          -- print (toModBxA (modSimp f))
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
              -- print folF
              -- print (simpFOLViz2 folF)
              (if simpFOLViz2 folF == Topc then do
                _ <- runGraphviz topViz Jpeg "FOLCorrVis.jpeg"
                putStrLn ("First-Order Correspondent: " ++ ppFOLForm (simpFOLViz2 folF))
              else (if simpFOLViz2 folF == Negc Topc then do
                      _ <- runGraphviz botViz Jpeg "FOLCorrVis.jpeg"
                      putStrLn ("First-Order Correspondent: " ++ ppFOLForm (simpFOLViz2 folF))
                    else do
                      putStrLn ("First-Order Correspondent: " ++ ppFOLForm folF)
                      (if clusterDepth (simpFOLViz2 folF) 0 < 3 then
                        (if not (impliedOrs (simpFOLViz2 folF)) then do
                          _ <- runGraphviz (toGraph (toClusters3 (simpFOLViz2 folF))) Pdf "FOLCorrVis.pdf"
                          _ <- runGraphviz (toGraph (toClusters3 (simpFOLViz2 folF))) Jpeg "FOLCorrVis.jpeg"
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
                
              
              
-- ((p-><>p)&(<>p->p))|((q-><><>q)&(<>q-><><>q)) equiv ((p-><>p)&(<>p->p))|((q|<>q)-><><>q)
-- ((<>[]p->[]<>p)&(p-><>p))|((<><>q-><>q)&(<>q-><><>q))
-- ((p-><>p)|(q-><><>q))&((<>p->p)|(<>q-><><>q))
-- p->(<>[]<>[]<>p|[]<>[]<>[]p)
-- (p|(<>p&~[]<>p))-><><>p

-- ~[]<>p & ([]p->p)
-- ([]((p|~<>p)->[]p))| ((q&<>q)->[]q)

-- ~(p&<><>p)->[]p      (~p|~<><>p)->[]p       (~p->[]p)&(~<><>p->[]p)     ([]p|p)&(<><>p|[]p)   ([]p&<><>p)|([]p)|(p&<><>p)|(p|[]p)
-- ([]p|<>(p&<>p)|~[]q)->p   ([]p|<>((p&<>p)|~q))->p

-- TOO MANY SUBCLUSTERS : ((p&<>p)|~<>p)-><>([]p|<>p) or ((p&<>p)|[]p)-><>([]p|[]<>p)
-- TOO MANY IMPLIED ORS (p&<>p&[]p&<>[]p)->[]<>p

-- (p&<>p&[]p)-><>([]p|[]<>p)
-- ((p&<>p&[]p)-><>[]p)|((q&<>q&[]q)-><>[]<>q)
-- TOO MANY IMPLIED ORS: (p&<>p&[]p&<><>p)-><>([]p|[]<>p)
-- TOO MANY SUBLUCTERS: ((p&<>p&[]p)-><>([]p|[]<>p))|(q-><>q) , p->(<>[]p|<>(<>p|[]<>p))


-- CURRENTLY (<>p-><>[]p)|(<>q->[]<>q) and <>p->(<>[]p|[]<>p) have SAME vis. but left is OR (...) right FORALL X1 OR (...)
-- Can we have exists xi disj? (If no, can reuse variable list in clusters to signify diff by forall xi disj (to distinguis from regular disj.))
