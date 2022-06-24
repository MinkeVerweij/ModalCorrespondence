{
{-# OPTIONS_GHC -w #-}
module Lex where
import Token
}

%wrapper "posn"

$dig = 0-9      -- digits
$alf = [a-zA-Z] -- alphabetic characters

tokens :-
  -- ignore whitespace and comments:
  $white+           ;
  "--".*            ;
  "("               { \ p _ -> TokenOB                p }
  ")"               { \ p _ -> TokenCB                p }
 "<>"              {\ p _ -> TokenDia                       p }
 "[]"              {\ p _ -> TokenBox                       p }
  "Top"             { \ p _ -> TokenTop               p }
  "Bot"             { \ p _ -> TokenBot               p }
  "~"               { \ p _ -> TokenNeg               p }
  "Not"             { \ p _ -> TokenNeg               p }
  "not"             { \ p _ -> TokenNeg               p }
  "&"               { \ p _ -> TokenBinCon            p }
  "|"               { \ p _ -> TokenBinDis            p }
  "->"              { \ p _ -> TokenImpl              p }
  "iff"             { \ p _ -> TokenBiImpl              p }
 "p"                { \ p _ -> TokenPrpP              p }
 "q"                { \ p _ -> TokenPrpQ              p }
 "r"                { \ p _ -> TokenPrpR              p }
{
type LexResult a = Either (Int,Int) a

alexScanTokensSafe :: String -> LexResult [Token AlexPosn]
alexScanTokensSafe str = go (alexStartPos,'\n',[],str) where
  go inp@(pos,_,_,str) =
    case (alexScan inp 0) of
      AlexEOF -> Right []
      AlexError ((AlexPn _ line column),_,_,_) -> Left (line,column)
      AlexSkip  inp' len     -> go inp'
      AlexToken inp' len act -> case (act pos (take len str), go inp') of
        (_, Left lc) -> Left lc
        (x, Right y) -> Right (x : y)
}