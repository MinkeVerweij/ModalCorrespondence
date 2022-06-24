{
{-# OPTIONS_GHC -w #-}
module Parse where
import Token
import Lex
import Languages
}

%name parse ModForm
%tokentype { Token AlexPosn }
%error { parseError }

%monad { ParseResult } { >>= } { Right }

%token
 'p'      {TokenPrpP  _}
 'q'      {TokenPrpQ  _}
 'r'      {TokenPrpR  _}

  TOP    { TokenTop    _ }
  BOT    { TokenBot    _ }
  '('    { TokenOB     _ }
  ')'    { TokenCB     _ }
  '<>'    { TokenDia     _ }
  '[]'    { TokenBox     _ }
  '&'    { TokenBinCon _ }
  '|'    { TokenBinDis _ }
  '~'    { TokenNeg    _ }
  '->'   { TokenImpl   _ }
  'iff'  { TokenBiImpl   _ }


%left '->' 'iff'
%left '|' '&'
%nonassoc '&' '|'
%left '~' '<>' '[]'



%%

ModForm : TOP { Top }
     | BOT { Not Top }
     | '(' ModForm ')' { $2 }
     | '~' ModForm { Not $2 }
     | ModForm '&' ModForm { Con $1 $3 }
     | ModForm '|' ModForm {  Not (Con (Not $1) (Not $3)) }
     | ModForm '->' ModForm { Not (Con $1 (Not $3)) }
     | ModForm 'iff' ModForm { biImp $1 $3 }
     | 'p' {Prp 0}
     | 'q' {Prp 1}
     | 'r' {Prp 2}
     | '<>' ModForm {dia $2}
     | '[]' ModForm {Box $2}
{

type ParseResult a = Either (Int,Int) a

parseError :: [Token AlexPosn] -> ParseResult a
parseError []     = Left (1,1)
parseError (t:ts) = Left (lin,col)
  where (AlexPn abs lin col) = apn t
}