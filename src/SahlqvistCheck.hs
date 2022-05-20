module SahlqvistCheck where
import Languages
import Data.List

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
isSqBxA (ConBxA f g) = isSqBxA f && isSqBxA g
isSqBxA (Nbox _ f) = isSqBxA f
isSqBxA f | isNegativeBxA f && isSqAntBxA (NotBxA f) = True -- monotone negative
        | isNegativeBxA (NotBxA f) = True -- mono. pos
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
isNegativeBxA (NotBxA (Nbox _ f)) = not (isNegativeBxA f)
isNegativeBxA (NotBxA (ConBxA f g)) = neither (isNegativeBxA f) (isNegativeBxA g)
isNegativeBxA (NotBxA (NotBxA f)) = isNegativeBxA f
isNegativeBxA (ConBxA f g) = isNegativeBxA f && isNegativeBxA g
isNegativeBxA (Nbox _ f) = isNegativeBxA f

neither :: Bool -> Bool -> Bool
neither False False = True
neither _ _ = False

-- get propositions from Modal Formula (for disj. Sq formulas)
props :: ModFormBxA -> [Int]
props (PrpBxA k) = [k]
props (ConBxA f g) = props f ++ props g
props (NotBxA f) = props f
props (Nbox _ f) = props f
props _ = []
