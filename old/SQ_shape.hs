module SQ_shape where

import Languages

import Data.List


isSq :: ModForm -> Bool
isSq Top = True
isSq (Not Top) = True
isSq (Prp _) = False
isSq (Not (Not f)) = isSq f
isSq (Not (Con f g)) = isSqAnt f && isNegative g || -- f -> ~g
    isSqAnt g && isNegative f -- g -> ~f

-- isSq (Not (Con (Not f) (Not g))) = (noSharedPrp f g) && (isSq f) && (isSq g) -- f \or g
-- isSq (Not _) = False
-- isSq (Con f g) = (isSq f) && (isSq g)
-- isSq (Box f) = isSq f

isSq _ = False -- very simple

isSqAnt :: ModForm -> Bool -- very simple now
isSqAnt (Prp _) = True
isSqAnt Top = True
isSqAnt (Not Top) = True
isSqAnt (Not (Not f)) = isSqAnt f
isSqAnt (Not (Box (Box f))) = isSqAnt (Not f) -- ~[][] = <><>~
isSqAnt (Not (Box (Not f))) = isSqAnt f -- ~[]~ = <>
isSqAnt (Con f g) = isSqAnt f && isSqAnt g
isSqAnt (Box f) = isBoxAt f
isSqAnt _ = False -- VS

isBoxAt :: ModForm -> Bool
isBoxAt (Prp _) = True
isBoxAt (Box f) = isBoxAt f
isBoxAt _ = False


sq_t :: [Bool]
sq_t = [(isSq (imp (Prp 0) (dia (Prp 0)))), -- VS
    (isSq (dis (Box (Prp 0)) (Not (Prp 0)))), -- VS
    (isSq (Not (Con (Not (Not (Prp 0))) (Not (Box (Prp 0)))))), -- VS
    (isSq (imp (Prp 0) (dis (Prp 0) (Prp 1)))), -- VS
    (isSq (imp (Prp 0) (imp (Not (Prp 1)) (Prp 2)))), --VS
    (isSq (Not (Not (imp (Con (dia (dia (Prp 0))) (Prp 1)) (dia (dia (Box (Prp 0)))))))), --VS
    (isSq ((imp (Box (Prp 0)) (Box (Box (Prp 0)))))), -- S
    (isSq ((Box (imp (Prp 0) (dia (Prp 0)))))), -- N
    (isSq ((imp (Con (Prp 0) (dia (Not (Prp 0)))) (dia (Prp 0))))) --N
    ]



noSharedPrp :: ModForm -> ModForm -> Bool
noSharedPrp f g = intersect (prpInMForm f) (prpInMForm g) == []

prpInMForm :: ModForm -> [Int]
prpInMForm = undefined


xOR :: Bool -> Bool -> Bool
xOR True False = True
xOR False True = True
xOR _ _ = False



isPositive :: ModForm -> Bool
isPositive Top = True
isPositive (Not Top) = True
isPositive (Prp _) = True
isPositive (Not (Prp _)) = False
isPositive (Not (Box f)) = not (isPositive f)
isPositive (Not (Con f g)) = neither (isPositive f) (isPositive g)
isPositive (Not (Not f)) = isPositive f
isPositive (Con f g) = isPositive f && isPositive g
isPositive (Box f) = isPositive f


pos_t :: [Bool]
pos_t = [
    isPositive (dis (Not (Prp 0)) (Not (Prp 1))),
    isPositive (dis (Prp 0) (Not (Prp 1))),
    isPositive (Con (Not (Prp 0)) (Not (Prp 1))),
    isPositive (Not (Con (Not (Not (Prp 0))) (Not (Not (Prp 1))))),
    isPositive (Not (Con (Not (Prp 0)) (Prp 1))),
    isPositive (Not (dis (Not (Prp 0)) (Not (Prp 1)))),
    isPositive (imp (Not (Prp 0)) (Prp 1)),
    isPositive (Not (dia (Box (Not (dis (Prp 0) (Prp 1)))))),
    isPositive (dia (Box (dis (Prp 0) (Prp 1))))
    ]

isNegative:: ModForm -> Bool
isNegative Top = True
isNegative (Not Top) = True
isNegative (Prp _) = False
isNegative (Not (Prp _)) = True
isNegative (Not (Box f)) = not (isNegative f)
isNegative (Not (Con f g)) = neither (isNegative f) (isNegative g)
isNegative (Not (Not f)) = isNegative f
isNegative (Con f g) = isNegative f && isNegative g
isNegative (Box f) = isNegative f

neg_t :: [Bool]
neg_t = [
    isNegative (dis (Not (Prp 0)) (Not (Prp 1))),
    isNegative (dis (Prp 0) (Not (Prp 1))),
    isNegative (Con (Not (Prp 0)) (Not (Prp 1))),
    isNegative (Not (Con (Not (Not (Prp 0))) (Not (Not (Prp 1))))),
    isNegative (Not (Con (Not (Prp 0)) (Prp 1))),
    isNegative (Not (dis (Not (Prp 0)) (Not (Prp 1)))),
    isNegative (imp (Not (Prp 0)) (Prp 1)),
    isNegative (dia (Box (Not (dis (Prp 0) (Prp 1))))),
    isNegative (Not (dia (Box (dis (Prp 0) (Prp 1)))))
    ]
