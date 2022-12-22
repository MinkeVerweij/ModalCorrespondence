{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE CPP #-}

module Main where

import Miso
import Miso.String

#ifndef __GHCJS__
import Language.Javascript.JSaddle.Warp as JSaddle
#endif

-- Standard imports

-- import Data.GraphViz.Commands -- TODO below!

-- Imports from our own library
import Lex
import Parse
import Languages
import ModalSimplify
import FOLCorrespondent
import SahlqvistCheck
import FOLSimplify

-- Needed for JSaddle:
#ifndef __GHCJS__
runApp :: JSM () -> IO ()
runApp f = JSaddle.debugOr 8080 (f >> syncPoint) JSaddle.jsaddleApp
#else
runApp :: IO () -> IO ()
runApp app = app
#endif

-- | (Current input, currently used string)
type Model = (MisoString, ModForm)

data Action
  = NoOp
  | SetInput MisoString
  deriving (Show, Eq)

start :: Model
start = ("p -> <><>p", Prp 1) -- FIXME ?

-- | Entry point for a miso application
main :: IO ()
main = runApp $ startApp App {..}
  where
    initialAction = NoOp            -- initial action to be executed on application load
    model  = start                  -- initial model
    update = updateModel            -- update function
    view   = viewModel              -- view function
    events = defaultEvents          -- default delegated events
    subs   = []                     -- empty subscription list
    mountPoint = Nothing            -- mount point for application (Nothing defaults to 'body')
    logLevel = Off                  -- used during prerendering to see if the VDOM and DOM are in sync (only applies to `miso` function)

-- | Updates model, optionally introduces side effects
updateModel :: Action -> Model -> Effect Action Model
updateModel action m@(oldIS, oldS) =
  case action of
    NoOp
      -> noEff m
    SetInput newIS
      -> noEff (newIS, case parseInput (fromMisoString newIS) of
                          Left _ -> oldS
                          Right f -> f)

parseInput :: String -> Either String ModForm
parseInput input =
  case alexScanTokensSafe input of
    Left (_,col) -> Left $ "Lex error at position " ++ show col
    Right tokenList ->
      case Parse.parse tokenList of
        Left (_,col) -> Left $ "Parse error at position " ++ show col
        Right f -> Right f

-- | Constructs a virtual DOM from a model
viewModel :: Model -> View Action
viewModel (is, f) = div_ [] [
   text "Welcome! Please enter a modal formula here: "
 , br_ []
 , input_ [ value_ is, onInput SetInput ]
 , text . ms $ case parseInput (fromMisoString is) of
                 Left e -> " " ++ e -- TOOD: make error orange
                 Right _ -> ""
 , br_ []
 , pre_ [] [ text (ms $ result f) ]
 -- TODO: show picture!
 ]

-- adapted from the CLI main
result :: ModForm -> String
result f =
          ("Input: " ++ ppModForm f) -- confirm input
          ++ "\n" ++
          case getSqBxA1 (toModBxA (modSimp f)) of
            Nothing ->
              "Not Sahlqvist. Not uniform. No Correspondent found."
            Just folF ->
              (if isSqBxA (toModBxA (modSimp f)) then "Sahlqvist." else "Not Sahlqvist")
              ++ "\n" ++
              (if isUniform (toModBxA (modSimp f)) then "Uniform." else "Not uniform.")
              ++ "\n" ++
              ("First-Order Correspondent: " ++ ppFOLForm (simpFOLViz2 folF))
{-
              (if simpFOLViz2 folF == Topc then do
                _ <- runGraphviz topViz Pdf "FOLCorrVis.pdf"
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
-}
