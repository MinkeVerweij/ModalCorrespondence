
-- module E2 where

import Data.List
-- import Test.QuickCheck

-- newtype UnOrdPair a = UOP (a,a)

-- instance (Show a, Ord a) => Show (UnOrdPair a) where
--   show (UOP (x,y)) | x < y = "(" ++ show x ++ "," ++ show y ++ ")"
--     | otherwise =  "(" ++ show y ++ "," ++ show x ++ ")"

-- instance Ord a => Eq (UnOrdPair a) where
--   (==) (UOP (x1,y1)) (UOP (x2,y2)) = (x1 == x2 && y1 == y2) || (x1 == y2 && y1 == x2) 

-- luhn :: Integer -> Bool
-- luhn n = checkdigit (init (digits n)) == last (digits n)

-- digits :: Integer -> [Integer]
-- digits n = map (\x -> read [x]) (show n)

-- checkcalcsum :: [Integer] -> Integer
-- checkcalcsum ls = sum [sum (digits n) | n <- doubleEveryOthR ls]

-- checkdigit :: [Integer] -> Integer
-- checkdigit ls = 10 - (mod (checkcalcsum ls) 10)

-- doubleEveryOthR :: [Integer] -> [Integer]
-- doubleEveryOthR ls = reverse $ doubleEveryOthL (reverse ls)

-- doubleEveryOthL :: [Integer] -> [Integer]
-- doubleEveryOthL [] = []
-- doubleEveryOthL [x] = [2*x]
-- doubleEveryOthL (x:y:xs) = [2*x, y] ++ doubleEveryOthL xs

-- isAmericanExpress, isMaster, isVisa :: Integer -> Bool
-- isAmericanExpress = undefined
-- isMaster = undefined
-- isVisa = undefined

-- -- X-ing game

-- data Item =  Wolf | Goat | Cabbage | Farmer deriving (Eq,Show)
-- data Position = L | R deriving (Eq,Show)
-- type State = ([Item], [Item])

-- start :: State
-- start = ([Wolf,Goat,Cabbage,Farmer], [])

-- type Move = (Position, Maybe Item)

-- move :: State -> Move -> State
-- move (l,r) (L, Just  a) = (l ++ [Farmer,a], r \\ [Farmer,a])
-- move (l,r) (L, Nothing) = (l ++ [Farmer], r \\ [Farmer])
-- move (l,r) (R, Just a) =  (l \\ [Farmer,a], r ++ [Farmer,a])
-- move (l,r) (R, Nothing) = (l \\ [Farmer], r ++ [Farmer])

-- someoneGetsEaten ::[Item] -> Bool
-- someoneGetsEaten xs = ((elem Wolf xs) && (elem Goat xs)) && not (elem Farmer xs)
--  || ((elem Goat xs) && (elem Cabbage xs))  && not (elem Farmer xs)

-- isBad, isSolved :: State -> Bool
-- isBad    (l,r) = someoneGetsEaten l || someoneGetsEaten r
-- isSolved (l,_) = null l

-- availableMoves :: State -> [Move]
-- availableMoves (l,_) | (elem Farmer l) = map (getMove R) (map Just (l \\ [Farmer])) ++ [(R, Nothing)]
-- availableMoves (_,r) | (elem Farmer r) = map (getMove L) (map Just (r \\ [Farmer])) ++ [(L, Nothing)]
-- availableMoves (_,_) = undefined

-- getMove :: Position -> Maybe Item -> Move
-- -- Can this be shorter, e.g. getMove dir ... = (dir, ...) w/ dir in {L, R}
-- getMove L Nothing = (L, Nothing)
-- getMove L (Just a) = (L, Just a)
-- getMove R Nothing = (R, Nothing)
-- getMove R (Just a) = (R, Just a)



-- solve :: [State] -> State -> [[Move]]
-- solve prev s | isSolved s = [ [] ]
--              | otherwise  = [ m : nexts | m <- availableMoves s
--                                         , not (elem (move s m) prev) -- do not move into "prev"
--                                         , not (isBad (move s m)) -- avoid if state isBad
--                                         , nexts <- solve (s:prev) (move s m) ]

-- allSolutions :: [[Move]]
-- allSolutions = solve [] start

-- firstSolution :: [Move]
-- firstSolution = head allSolutions


-- MODAL LOGIC

type World = Integer
type Universe = [World]
type Proposition = Int
type Valuation = World -> [Proposition]
type Relation = [(World,World)]
data KripkeModel = KrM Universe Valuation Relation

data ModForm = Prp Proposition
             | Not ModForm
             | Con ModForm ModForm
             | Box ModForm
             | Top
             deriving (Eq,Ord,Show)

myModel :: KripkeModel
myModel = KrM [0,1,2] myVal myRel where
  myRel = [(0,0),(0,1),(0,2)]
  myVal 0 = [1,2]
  myVal 1 = [1]
  myVal 2 = [1,3]
  myVal _ = undefined

makesTrue :: (KripkeModel,World) -> ModForm -> Bool
makesTrue _ Top = True
makesTrue (KrM _ v _, w) (Prp k)   = k `elem` v w
makesTrue (m,w)          (Not f)   = not (makesTrue (m,w) f)
makesTrue (m,w)          (Con f g) =
  makesTrue (m,w) f && makesTrue (m,w) g
makesTrue (KrM u v r, w) (Box f)   =
  all (\w' -> makesTrue (KrM u v r,w') f) ws where
    ws = [ y | y <- u, (w,y) `elem` r ]

trueEverywhere :: KripkeModel -> ModForm -> Bool
trueEverywhere (KrM u v r) f = all (\w' -> makesTrue (KrM u v r,w') f) u

-- trueEverywhere tests
truth_t :: [Bool]
truth_t = [
  trueEverywhere myModel1 (dis (Prp 1) (dia (Prp 1))),
  trueEverywhere myModel1 (imp (Prp 2) (dia (Box (Not Top))))
  ]
dia :: ModForm -> ModForm
dia f = (Not (Box (Not f)))

dis :: ModForm -> ModForm -> ModForm
dis f g = (Not (Con (Not f) (Not g)))

imp :: ModForm -> ModForm -> ModForm
imp f g = (Not (Con f (Not g)))

bot :: ModForm
bot = (Not Top)


instance Eq KripkeModel where
    (==) (KrM u v r) (KrM u' v' r') = 
      (length u == length u') &&
      sort (map (\w -> (v w, (getWRVals w r v))) u) ==
         sort (map (\w' -> (v' w', (getWRVals w' r' v'))) u')
-- map (\t -> snd t) [(1,2)] gives [2]
-- filter (\t -> fst t == 1) [(1,2),(1,3),(2,1)] gives [(1,2),(1,3)]

-- test for Eq KripkeModel
myModel1 :: KripkeModel
myModel1 = KrM [0,1] myVal1 myRel1 where
  myRel1 = [(0,0),(0,1)]
  myVal1 0 = [2]
  myVal1 1 = [1]
  myVal1 _ = undefined

myModel2 :: KripkeModel
myModel2 = KrM [2,3] myVal2 myRel2 where
  myRel2 = [(2,3),(2,2)]
  myVal2 2 = [2]
  myVal2 3 = [1]
  myVal2 _ = undefined

getWRels :: World -> Relation -> Relation
getWRels w r = filter (\t -> fst t == w) r

getSuccWorlds :: World -> Relation -> [World]
getSuccWorlds w r = map (\t -> snd t) (getWRels w r)

gettoWRels :: World -> Relation -> Relation
gettoWRels w r = filter (\t -> snd t == w) r

getPrevWorlds :: World -> Relation -> [World]
getPrevWorlds w r = map (\t -> fst t) (gettoWRels w r)

getWRVals :: World -> Relation -> Valuation -> [[Proposition]]
getWRVals w r v = sort $ map v (map (\t -> snd t) (getWRels w r))

type Bisimulation = [(World,World)]

checkBisim :: KripkeModel -> KripkeModel -> Bisimulation -> Bool
checkBisim (KrM _ _ _) (KrM _ _ _) [] = False
checkBisim (KrM _ v r) (KrM _ v' r') bi = 
  all (\t -> v (fst t) == v' (snd t) && -- same valuations w,w' s.t. wBw'
 forth (getSuccWorlds (fst t) r) bi (snd t) r' && -- Rwv -> Ex(v'), vBv' and R'w'v' 
 back (getSuccWorlds (snd t) r') bi (fst t) r) bi -- R'w'v' -> Ex(v), vBv' and Rwv

-- checkBisim2 :: KripkeModel -> KripkeModel -> Bisimulation -> [Bool]
-- checkBisim2 (KrM _ v r) (KrM _ v' r') bi = sameVals v v' bi

-- sameVals :: Valuation -> Valuation -> Bisimulation -> [Bool]
-- sameVals v v' bi = map (\t -> v (fst t) == v' (snd t)) bi

forth :: [World] -> Bisimulation -> World -> Relation -> Bool
-- no succ. worlds
forth [] _ _ _ = True
-- Ex(v') vBv' and R'w'v'
forth (x:rws) b w' r' = or (map (\s -> elem s (getSuccWorlds w' r')) (getSuccWorlds x b)) &&
  forth rws b w' r'


back :: [World] -> Bisimulation -> World -> Relation -> Bool
-- no succ. worlds
back [] _ _ _ = True
-- Ex(v) vBv' and Rwv
back (x:rws) b w r = or (map (\s -> elem s (getSuccWorlds w r)) (getPrevWorlds x b)) &&
  back rws b w r


tests :: [Bool]
tests = [checkBisim myModel3 myModel4 [(1,2), (2,1), (3,1), (4,2)], -- True
  checkBisim myModel3 myModel4 [(1,2), (2,1), (4,2)], -- False, 2B1' + 2R3, NO v' s.t. 3Bv'
  checkBisim myModel3 myModel4 [(1,2), (4,2)], -- True, should it be?
  areBisim myModel myModel1, --True but should they? (share one bisim state so rel non-empty)
  myModel1 == myModel2, -- True
  myModel1 == myModel -- False
  ]
-- test for checkBisim
myModel3 :: KripkeModel
myModel3 = KrM [1,2,3,4] myVal3 myRel3 where
  myRel3 = [(2,1),(2,3),(3,2),(3,4)]
  myVal3 1 = []
  myVal3 2 = []
  myVal3 3 = []
  myVal3 4 = []
  myVal3 _ = undefined

myModel4 :: KripkeModel
myModel4 = KrM [1,2] myVal4 myRel4 where
  myRel4 = [(1,1),(1,2)]
  myVal4 1 = []
  myVal4 2 = []
  myVal4 _ = undefined

myBisim :: Bisimulation
myBisim = [(1,2), (2,1), (3,1), (4,2)]

areBisim :: KripkeModel -> KripkeModel -> Bool
areBisim (KrM u v r) (KrM u' v' r') = or (map (\b -> checkBisim (KrM u v r) (KrM u' v' r') b) (allRels u u'))

fullRels :: [World] -> [World] -> Relation
fullRels [] _ = []
fullRels _ [] = []
fullRels (x:xs) (y:ys) = [(x,y)] ++ fullRels xs [y] ++ fullRels [x] ys ++ fullRels xs ys
  
allSubRels :: Relation -> [Relation]
allSubRels [] = [[]]
allSubRels (x:xs) = map (x:) (allSubRels xs) ++ allSubRels xs

allRels :: [World] -> [World] -> [Relation]
allRels u u' = allSubRels (fullRels u u')

type EquiRel = [[World]]

data KripkeModelS5 = KrMS5 Universe Valuation EquiRel

makesTrueS5 :: KripkeModelS5 -> ModForm -> Bool
makesTrueS5 = undefined