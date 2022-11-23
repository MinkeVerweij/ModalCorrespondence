{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE CPP #-}

module Main where

import Miso
import Miso.String

#ifndef __GHCJS__
import Language.Javascript.JSaddle.Warp as JSaddle
#endif

-- | Standard imports

-- import Data.GraphViz.Commands -- TODO below!

-- | Imports from our own library
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

-- | Current input string
type Model = MisoString

data Action
  = NewString MisoString
  deriving (Show, Eq)

start :: MisoString
start = "p -> <><>p"

-- | Entry point for a miso application
main :: IO ()
main = runApp $ startApp App {..}
  where
    initialAction = NewString start -- initial action to be executed on application load
    model  = start                  -- initial model
    update = updateModel            -- update function
    view   = viewModel              -- view function
    events = defaultEvents          -- default delegated events
    subs   = []                     -- empty subscription list
    mountPoint = Nothing            -- mount point for application (Nothing defaults to 'body')
    logLevel = Off                  -- used during prerendering to see if the VDOM and DOM are in sync (only applies to `miso` function)

-- | Updates model, optionally introduces side effects
updateModel :: Action -> Model -> Effect Action Model
updateModel action _ =
  case action of
    NewString s
      -> noEff s

-- | Constructs a virtual DOM from a model
viewModel :: Model -> View Action
viewModel s = div_ [] [
   text "Welcome! Please enter a modal formula here: "
 , input_ [ value_ s, onInput NewString ]
 , br_ []
 , pre_ [] [ text (ms . result . fromMisoString $ s) ]
 ]

-- adapted from the CLI main
result :: String -> String
result input =
  case alexScanTokensSafe input of
    Left (line,col) -> "Lex error in line " ++ show line ++ " at column " ++ show col
    Right tokenList ->
      case Parse.parse tokenList of
        Left p -> "error at " ++ show p
        Right f ->
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
