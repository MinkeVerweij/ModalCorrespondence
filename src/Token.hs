module Token where
data Token a
 = TokenTop               {apn :: a}
  | TokenBot               {apn :: a}
  | TokenPrpP               {apn :: a}
  | TokenPrpQ               {apn :: a}
  | TokenPrpR               {apn :: a}
  | TokenNeg               {apn :: a}
  | TokenOB                {apn :: a}
  | TokenCB                {apn :: a}
  | TokenDia              {apn :: a}
  | TokenBox              {apn :: a}
  | TokenBinCon            {apn :: a}
  | TokenBinDis            {apn :: a}
  | TokenImpl              {apn :: a}
  | TokenBiImpl              {apn :: a}
  deriving (Eq,Show)