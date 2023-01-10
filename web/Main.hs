{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Main where

#ifndef __GHCJS__
import Language.Javascript.JSaddle.Warp as JSaddle
#endif

import Data.GraphViz.Commands
import Data.GraphViz.Types
import Data.Text.Lazy
import Miso
import Miso.String
import System.IO.Temp
import System.IO.Unsafe

import FOLCorrespondent
import FOLSimplify
import Languages
import Lex
import MakeViz
import ModalSimplify
import Parse
import SahlqvistCheck

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
start = ("<>p -> []<>p", Prp 1)

-- | Entry point for a miso application
main :: IO ()
main = runApp $ startApp App {..}
  where
    initialAction = SetInput "<>p -> []<>p" -- initial action to be executed on application load
    model = start -- initial model
    update = updateModel -- update function
    view = viewModel -- view function
    events = defaultEvents -- default delegated events
    subs = [] -- empty subscription list
    mountPoint = Nothing -- mount point for application (Nothing defaults to 'body')
    logLevel = Off -- used during prerendering to see if the VDOM and DOM are in sync (only applies to `miso` function)

-- | Updates model, optionally introduces side effects
updateModel :: Action -> Model -> Effect Action Model
updateModel action m@(oldIS, oldS) =
  case action of
    NoOp ->
      noEff m
    SetInput newIS ->
      noEff
        ( newIS,
          case parseInput (fromMisoString newIS) of
            Left _ -> oldS
            Right f -> f
        )

parseInput :: String -> Either String ModForm
parseInput input =
  case alexScanTokensSafe input of
    Left (_, col) -> Left $ "Lex error at position " ++ show col
    Right tokenList ->
      case Parse.parse tokenList of
        Left (_, col) -> Left $ "Parse error at position " ++ show col
        Right f -> Right f

-- | Constructs a virtual DOM from a model
viewModel :: Model -> View Action
viewModel (is, f) =
  div_
    [class_ "container"]
    $ [ rawHtml $ ms $ "<style>" ++ myCss ++ "</style>",
        script,
        h1_ [] [text "Modal Correspondence Online"],
        p_ [] [text "Welcome! Please enter a modal formula here: "],
        input_ [value_ is, onInput SetInput],
        case parseInput (fromMisoString is) of
          Left e -> span_ [class_ "error"] [text . ms $ " " ++ e]
          Right _ -> text "",
        br_ []
      ]
      ++ result f

myCss :: String
myCss =
  Prelude.concat $
    [ " body { font-family: sans; } ",
      " .error { color: red; } ",
      " h1, p, margin { margin-bottom:5px; }",
      " h1 { font-weight: bold; font-size:120%; }",
      " input { padding:10px; font-size: 110%; width: 50%; max-width:400px; } "
    ]

p :: String -> View Action
p s = p_ [] [text . ms $ s]

-- adapted from the CLI main
result :: ModForm -> [View Action]
result f =
  [ p $ "Input: " ++ ppModForm f,
    p $ "Simplified: " ++ ppModForm (modSimp f)
    -- , p $ "Converted: " ++  show (toModBxA (modSimp f)) -- TODO: needs ppModFormBxA
  ]
    ++ case getSqBxA1 (toModBxA (modSimp f)) of
      Nothing ->
        [p "Not Sahlqvist. Not uniform. No Correspondent found."]
      Just folF ->
        [ p $ if isSqBxA (toModBxA (modSimp f)) then "Sahlqvist." else "Not Sahlqvist.",
          p $ if isUniform (toModBxA (modSimp f)) then "Uniform." else "Not uniform.",
          p $ "First-Order Correspondent: " ++ ppFOLForm folF,
          p $ "Simplified: " ++ ppFOLForm (simpFOLViz2 folF),
          br_ []
        ]
          ++ case simpFOLViz2 folF of
            Topc -> return . p $ "Top"
            Negc Topc -> return . p $ "Bot"
            _ | clusterDepth (simpFOLViz2 folF) 0 >= 3 ->
                  return $ p "Cannot visualize this, too many subclusters."
            _ | impliedOrs (simpFOLViz2 folF) ->
                  return $ p "Cannot visualize this, too many implied disjuncts."
            _ ->
              [ div_ [id_ "graph"] [text "..."]
              , rawHtml (ms $ scriptInline thedot)
              -- , pre_ [] . return . text . ms $ thedot
              ] where thedot = Data.Text.Lazy.unpack $ printDotGraph (toGraph (toClusters3 (simpFOLViz2 folF)))

script =
  rawHtml . ms $
    "<script src=\"https://github.com/mdaines/viz.js/releases/download/v2.1.2/viz.js\"></script>\n"
    ++ "<script src=\"https://github.com/mdaines/viz.js/releases/download/v2.1.2/full.render.js\"></script>"

scriptInline :: String -> String
scriptInline dot =
  Prelude.unlines
    [ "<script>"
    , "function sleep(ms) { return new Promise(resolve => setTimeout(resolve, ms)); }"
    , "async function doViz(dot) {"
    , "  document.getElementById('graph').innerHTML = 'Generating visualisation, please wait ...';"
    , "  await sleep(5000);"
    , "  let viz = new Viz( ); "
    , "  viz.renderSVGElement('" ++ Prelude.filter (/='\n') dot ++ "')"
    , "  .then(function(element) { "
    , "    document.getElementById('graph').innerHTML = '';"
    , "    document.getElementById('graph').appendChild(element); "
    , "  }) "
    , "  .catch(error => { "
    , "    // Possibly display the error "
    , "    console.error(error); "
    , "  }); "
    , "}"
    , "doViz();"
    , "</script>"
    ]
