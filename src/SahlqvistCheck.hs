module SahlqvistCheck where
import Languages
import Data.List
import Data.Bits
{- 
    Functions to check whether modal formula is Sahlqvist
-}
isSqBxA :: ModFormBxA -> Bool
isSqBxA TopBxA = True
isSqBxA (NotBxA TopBxA) = True
isSqBxA (NotBxA (NotBxA f)) = isSqBxA f
isSqBxA (NotBxA (ConBxA f g)) = 
    isSqAntBxA f && isNegativeBxA g -- f -> ~g
    || isSqAntBxA g && isNegativeBxA f -- g -> ~f
    || isSqBxA (NotBxA f) && isSqBxA (NotBxA g) -- ~(~f & ~g) both Sq + no shared props
    &&  null (props f `intersect` props g) 
    || isNegativeBxA  (NotBxA (ConBxA  f g)) -- ~(f & g) mono. neg.
    && isSqAntBxA (ConBxA  f g)
    || isSqAntBxA (ConBxA f g) -- (~ h -> \bot)
isSqBxA (ConBxA f g) = isSqBxA f && isSqBxA g
isSqBxA (Nbox _ f) = isSqBxA f
isSqBxA f | isSqAntBxA (NotBxA f) = True -- (~ f -> \bot)
        | isNegativeBxA (NotBxA f) = True -- mono. pos : T -> f
isSqBxA _ = False

isSqAntBxA :: ModFormBxA -> Bool
isSqAntBxA TopBxA = True
isSqAntBxA (NotBxA TopBxA) = True
isSqAntBxA (PrpBxA _) = True 
isSqAntBxA (NotBxA (NotBxA f)) = isSqAntBxA f
isSqAntBxA (NotBxA (Nbox _ (NotBxA f))) = isSqAntBxA f
isSqAntBxA (NotBxA (Nbox _ (ConBxA f g))) = isSqAntBxA (NotBxA f) && isSqAntBxA (NotBxA g)
isSqAntBxA (ConBxA f g) = isSqAntBxA f && isSqAntBxA g
isSqAntBxA (Nbox _ (PrpBxA _)) = True -- Boxed atoms
isSqAntBxA (NotBxA (ConBxA f g)) = isSqAntBxA (NotBxA f) && isSqAntBxA (NotBxA g)  -- disj
isSqAntBxA f | isNegativeBxA f = True
            | otherwise = False

-- checks whether formula is uniformly negative
isNegativeBxA:: ModFormBxA -> Bool
isNegativeBxA TopBxA = True
isNegativeBxA (NotBxA TopBxA) = True
isNegativeBxA (PrpBxA _) = False
isNegativeBxA (NotBxA (PrpBxA _)) = True
isNegativeBxA (NotBxA (Nbox _ (NotBxA f))) = isNegativeBxA f
isNegativeBxA (NotBxA (Nbox _ f)) = isNegativeBxA (NotBxA f)
isNegativeBxA (NotBxA (ConBxA f g)) = isNegativeBxA (NotBxA f) && isNegativeBxA (NotBxA g) && isUniform f && isUniform g
isNegativeBxA (NotBxA (NotBxA f)) = isNegativeBxA f
isNegativeBxA (ConBxA f g) = isNegativeBxA f && isNegativeBxA g
isNegativeBxA (Nbox _ f) = isNegativeBxA f

neither :: Bool -> Bool -> Bool
neither False False = True
neither _ _ = False

isUniform:: ModFormBxA -> Bool
isUniform f = all  (`propUniform` f) (nub (props f))

propUniform :: Int -> ModFormBxA -> Bool
propUniform k f = propPosNeg  k f True || propPosNeg  k f False

-- if Prp k occurs pos in f: propPosNeg k f True --> True
-- if Prp k occurs neg in f: propPosNeg k f False --> True
propPosNeg :: Int -> ModFormBxA -> Bool -> Bool
propPosNeg  _ TopBxA _ = True
propPosNeg  _ (PrpBxA _) c = c
propPosNeg  k (NotBxA f) c | k `elem` props f =  propPosNeg  k f (c `xor` True)
                            | otherwise = c
propPosNeg  k (ConBxA f g) c | k `elem` props f && k `elem` props g = propPosNeg  k f c && propPosNeg  k g c
        | k `elem` props f = propPosNeg k f c
        | k `elem` props g = propPosNeg k g c
        | otherwise = c
propPosNeg  k (Nbox _ f) c = propPosNeg  k f c

-- get propositions from Modal Formula (for disj. Sq formulas)
props :: ModFormBxA -> [Int]
props (PrpBxA k) = [k]
props (ConBxA f g) = props f ++ props g
props (NotBxA f) = props f
props (Nbox _ f) = props f
props _ = []

-- props (ConBxA (PrpBxA 0) (disBxA (PrpBxA 1) (PrpBxA 0)))