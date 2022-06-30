module FOLCorrespondent where
import Languages
import SahlqvistCheck
import StandTrans
import Data.List
import Data.Maybe
import Instantiation
import FOLSimplify
import ModalSimplify
-- import Data.List

-- main algorithm: returns whether Sq + FOL correspondent if so
getSqBxA1 :: ModFormBxA -> Maybe FOLForm
getSqBxA1 f | isJust (getSqBxA f) = Just (simpFOL3 (fromJust (getSqBxA f)))
            | otherwise = Nothing

getSqBxA :: ModFormBxA -- returns Sq correspondent if any
  -> Maybe FOLForm
getSqBxA f | isUniform f = Just (getFOLuniform f)
getSqBxA TopBxA = Just Topc
getSqBxA (NotBxA TopBxA) = Just (Negc Topc)
getSqBxA (PrpBxA _) = Just (Negc Topc) -- p = T -> p
getSqBxA (NotBxA (PrpBxA _)) = Just (Negc Topc)
getSqBxA (NotBxA (NotBxA f)) = getSqBxA f
getSqBxA (NotBxA (ConBxA f g)) |
    isSqAntBxA f && isNegativeBxA g =  Just (getFOLimp f (NotBxA g))-- f -> ~g
    | isSqAntBxA g && isNegativeBxA f =  Just (getFOLimp g (NotBxA f))-- g -> ~f
    | (isSqBxA (NotBxA f) || isUniform f) && 
        (isSqBxA (NotBxA g) || isUniform g) &&  
        null (props f `intersect` props g) = -- ~(~f & ~g) both Sq + no shared props
            Just (getFOLdisj (NotBxA f) (NotBxA g))
getSqBxA (ConBxA f g) | (isSqBxA f || isUniform f) &&
                         (isSqBxA g || isUniform g) = Just (getFOLconj f g)
getSqBxA (Nbox n f) | isSqBxA f = Just (getFOLboxed n f)
getSqBxA f  | isSqAntBxA (NotBxA f) = Just (getFOLimp (boxModSimp (NotBxA f)) (NotBxA TopBxA))
getSqBxA _ = Nothing

getFOLuniform :: ModFormBxA -> FOLForm
getFOLuniform f = simpFOL3 (stUniform f f (V 0) [0])

{- 
    functions to get FOL corr. of implication 
        antecedent made up of {T,\bot, <>, BoxedAtoms, &, |, Neg. formulas}
        latter 2 require extra processing
-}
-- input :: Sq impl (S)
-- output :: FOL correspondent (unsimplified)
getFOLcorr :: ModFormBxA -> FOLForm
getFOLcorr f = instantiate1 (getPullDsFOL f) (getSubstitutionsFromAnt f)

-- get FO corresp. for Sq implication, becomes multiple when OR in antecedent
getFOLimp :: ModFormBxA -> ModFormBxA -> FOLForm -- f -> g Sq
getFOLimp f g = case splitOrAnt f of
  [_] -> getFOLcorrNegAnt f g
  fis -> Conjc (allFreshVars [getFOLcorrNegAnt fi g| fi <- fis] [0])

-- move negative part of antecedent to consequent
getFOLcorrNegAnt :: ModFormBxA -> ModFormBxA -> FOLForm
getFOLcorrNegAnt f g 
    | getPositiveBxA f /= f = getFOLcorr (impBxA  (getPositiveBxA f) (disBxA (NotBxA (getNegativeBxA f)) g))
    | otherwise = getFOLcorr (impBxA f g)

allFreshVars :: [FOLForm] -> [Int] -> [FOLForm]
allFreshVars [] _ = []
allFreshVars (f:fs) vars = varsSub (vars \\ [0]) (getNthFresh (length (varsInFOLform f)) (vars ++ varsInFOLform f)) f : 
                                allFreshVars fs (nub (vars ++ varsInFOLform f))

-- get postive part (of antecedent, NO disjunctions)
getPositiveBxA :: ModFormBxA -> ModFormBxA
getPositiveBxA f | isNegativeBxA (NotBxA f) = f
                | isNegativeBxA f = TopBxA
getPositiveBxA (ConBxA f g) = boxModSimp (ConBxA (getPositiveBxA f) (getPositiveBxA g))
getPositiveBxA (Nbox n f) = boxModSimp (Nbox n (getPositiveBxA f))
getPositiveBxA (NotBxA (ConBxA f g)) = boxModSimp (NotBxA (ConBxA (getNegativeBxA f) (getNegativeBxA g)))
getPositiveBxA (NotBxA (Nbox n f)) = boxModSimp (NotBxA (Nbox n (getNegativeBxA f)))
getPositiveBxA _ = undefined

-- get negative part (of antecedent, NO disjunctions) to move to consequent
getNegativeBxA :: ModFormBxA -> ModFormBxA
getNegativeBxA f | isNegativeBxA f = f
                | isNegativeBxA (NotBxA f) = TopBxA
getNegativeBxA (ConBxA f g) = boxModSimp (ConBxA (getNegativeBxA f) (getNegativeBxA g))
getNegativeBxA (Nbox n f) = boxModSimp (Nbox n (getNegativeBxA f))
getNegativeBxA (NotBxA (ConBxA f g)) = boxModSimp (NotBxA (ConBxA (getPositiveBxA f) (getPositiveBxA g)))
getNegativeBxA (NotBxA (Nbox n f)) = boxModSimp (NotBxA (Nbox n (getPositiveBxA f)))
getNegativeBxA _ = undefined

-- ELIMINATING DISJUNCTION FROM ANTECEDENT by splitting into conjunction of separate implications
-- split the OR in antecedent to use ((f OR g) -> h) equiv ((f -> h) AND (g -> h))
splitOrAnt :: ModFormBxA -> [ModFormBxA]
splitOrAnt (NotBxA (NotBxA f)) = splitOrAnt f
splitOrAnt (NotBxA (ConBxA f g)) = splitOrAnt (NotBxA f) ++ splitOrAnt (NotBxA g)
splitOrAnt (NotBxA (Nbox n (ConBxA f g))) = map (NotBxA . boxJoin n . NotBxA) (splitOrAnt (NotBxA (ConBxA f g)))
splitOrAnt (NotBxA (Nbox n (NotBxA f))) =  map (NotBxA . boxJoin n . NotBxA) (splitOrAnt f)
splitOrAnt (Nbox n f) = map (boxJoin n) (splitOrAnt f)
splitOrAnt (ConBxA f g) = [ConBxA f1 g1 | f1<- splitOrAnt f, g1<- splitOrAnt g]
splitOrAnt (NotBxA f) = map NotBxA (splitOrAnt f)
splitOrAnt f = [f]

-- ensure boxed atoms are joined (i.e. Nbox n (Nbox k _) does NOT occur)
boxJoin :: Int -> ModFormBxA -> ModFormBxA
boxJoin n (Nbox m f) = Nbox (n+m) f
boxJoin n (NotBxA (NotBxA f)) = boxJoin n f
boxJoin n f = Nbox n f

{-  
    functions to get FOL corr. of conj/disj of Sq formulas
-}
-- get FO corr. of disj. of Sq formulas 
getFOLdisj :: ModFormBxA -> ModFormBxA -> FOLForm -- f | g both Sq
getFOLdisj f g = Disjc [fromJust (getSqBxA f), 
    varsSub ((varsInFOLform (fromJust (getSqBxA f)) `intersect` varsInFOLform (fromJust (getSqBxA f))) \\ [0])
        (getNthFresh (length ((varsInFOLform (fromJust (getSqBxA f)) `intersect` varsInFOLform (fromJust (getSqBxA f)))\\[0])) (varsInFOLform (fromJust (getSqBxA f)) ++ varsInFOLform (fromJust (getSqBxA g))))
        (fromJust (getSqBxA g))]


-- get FO corr. of conj. of Sq formulas
getFOLconj :: ModFormBxA -> ModFormBxA -> FOLForm -- f & g both Sq
getFOLconj f g = Conjc [fromJust (getSqBxA f), 
    varsSub ((varsInFOLform (fromJust (getSqBxA f)) `intersect` varsInFOLform (fromJust (getSqBxA f))) \\ [0])
        (getNthFresh (length ((varsInFOLform (fromJust (getSqBxA f)) `intersect` varsInFOLform (fromJust (getSqBxA f)))\\[0])) (varsInFOLform (fromJust (getSqBxA f)) ++ varsInFOLform (fromJust (getSqBxA g))))
        (fromJust (getSqBxA g))]

{-
    functions to get FOL corr. of boxed Sq formulas 
-}

-- Get Sq ant of BOXES(Sq formula)
-- functionally same as normal getSqBxA, but keeps track of variables
getSqBxAbox :: ModFormBxA -> Int -> [Int] -> FOLForm
getSqBxAbox TopBxA _ _ = Topc
getSqBxAbox (NotBxA TopBxA) _ _ = Negc Topc
getSqBxAbox (PrpBxA _) _ _ = Negc Topc -- p = T -> p
getSqBxAbox (NotBxA (NotBxA f)) x vars = getSqBxAbox f x vars
getSqBxAbox (NotBxA (ConBxA f g)) x vars |
    isSqAntBxA f && isNegativeBxA g =  varsSub -- f -> ~g
        (varsInFOLform (getFOLimp f (NotBxA g)) \\ [x])
        (getNthFresh (length (varsInFOLform (getFOLimp f (NotBxA g))) - 1) vars)
        (getFOLimp f (NotBxA g))
    | isSqAntBxA g && isNegativeBxA f =  varsSub -- g -> ~f
        (varsInFOLform (getFOLimp g (NotBxA f)) \\ [x])
        (getNthFresh (length (varsInFOLform (getFOLimp g (NotBxA f))) - 1) vars)
        (getFOLimp g (NotBxA f)) 
    | isSqBxA (NotBxA f) && isSqBxA (NotBxA g) &&  null (props f `intersect` props g) = -- ~(~f & ~g) both Sq + no shared props
            varsSub 
            (varsInFOLform (getFOLdisj (NotBxA f) (NotBxA g)) \\ [x])
            (getNthFresh (length (varsInFOLform (getFOLdisj (NotBxA f) (NotBxA g)))) vars)
            (getFOLdisj (NotBxA f) (NotBxA g))
getSqBxAbox (ConBxA f g) x vars | 
    isSqBxA f && isSqBxA g =
            varsSub 
            (varsInFOLform (getFOLconj f g) \\ [x])
            (getNthFresh (length (varsInFOLform (getFOLconj f g))) vars)
            (getFOLconj f g)
getSqBxAbox (Nbox n f) x vars | isSqBxA f = getFOLboxed1 n f x vars
getSqBxAbox f _ _ | isSqAntBxA (NotBxA f) =  getFOLimp (NotBxA f) (NotBxA TopBxA)
                    | isUniform f = getFOLuniform f
getSqBxAbox _ _ _= undefined

-- with Boxed At translation
getFOLboxed1 :: Int -> ModFormBxA -> Int -> [Int] -> FOLForm
getFOLboxed1 n f x vars = (\y -> Forallc [V y] 
    (Impc (boxedR n vars x y) 
        (varsSub [x] [y] (getSqBxAbox f x (vars ++ getNthFresh n vars))))) (last (getNthFresh n vars))

-- on first call at variable x (V 0)
getFOLboxed :: Int -> ModFormBxA -> FOLForm
getFOLboxed n f = getFOLboxed1 n f 0 [0]