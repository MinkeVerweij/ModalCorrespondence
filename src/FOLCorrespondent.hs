module FOLCorrespondent where
import Languages
import SahlqvistCheck
import StandTrans
import Data.List
import Data.Maybe
import Instantiation
import FOLSimplify
import ModalSimplify

-- main algorithm: returns whether Sq + FOL correspondent if so
getSqBxA1 :: ModFormBxA -> Maybe FOLFormVSAnt
getSqBxA1 f | isJust (getSqBxA f) = Just (simpFOL3 (fromJust (getSqBxA f)))
            | otherwise = Nothing

-- Forallc [] (Impc (Conjc []) 
--(Negc (Conjc [Negc (Forallc [V 1] (Impc (Rc (VT (V 0)) (VT (V 1))) (Disjc [Eqdotc (VT (V 0)) (VT (V 1))]))),Forallc [V 2] (Impc (Rc (VT (V 0)) (VT (V 2))) (Negc (Disjc [Eqdotc (VT (V 0)) (VT (V 2))])))])))

getSqBxA :: ModFormBxA -- returns Sq correspondent if any
  -> Maybe FOLFormVSAnt
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

-- isSqBxA (toModBxA (Not (Con (Prp 0) (Not (Box (Not (Prp 0)))))))

getFOLuniform :: ModFormBxA -> FOLFormVSAnt
getFOLuniform f = simpFOL3 (standTransBxAUniform f f (V 0) [0])
-- special case negative monotonic formulas (subst Px for x=x)
-- getFOLmonoNeg :: ModFormBxA -> FOLFormVSAnt
-- getFOLmonoNeg f = standTransBxAmonoNeg f (V 0) [0]

{- 
    functions to get FOL corr. of implication 
        antecedent made up of {T,\bot, <>, BoxedAtoms, &, |, Neg. formulas}
        latter 2 require extra processing
-}
-- input :: Sq impl (S)
-- output :: FOL correspondent (unsimplified)
getFOLcorr :: ModFormBxA -> FOLFormVSAnt
getFOLcorr f = instantiate1 (getPullDsFOL f) (getSubstitutionsFromAnt f)

-- get FO corresp. for Sq implication, becomes multiple when OR in antecedent
getFOLimp :: ModFormBxA -> ModFormBxA -> FOLFormVSAnt -- f -> g Sq
getFOLimp f g | length (splitOrAnt f) == 1 = getFOLcorrNegAnt f g
            | otherwise = Conjc [getFOLcorrNegAnt fi g| fi <- splitOrAnt f]

--- MOVING NEGATIVE FORMULAS FROM ANTECEDENT TO CONSEQUENT
-- move negative part of antecedent to consequent
getFOLcorrNegAnt :: ModFormBxA -> ModFormBxA -> FOLFormVSAnt
getFOLcorrNegAnt f g | getPositiveBxA f /= f = 
                        getFOLcorr (impBxA  (getPositiveBxA f) (disBxA (NotBxA (getNegativeBxA f)) g))
                    | otherwise = getFOLcorr (impBxA f g)

-- getFOLcorrNegAnt1 :: ModFormBxA -> ModFormBxA -> ModFormBxA
-- getFOLcorrNegAnt1 f _ = f
-- getFOLcorrNegAnt2 :: ModFormBxA -> ModFormBxA -> ModFormBxA
-- getFOLcorrNegAnt2 _ f = f

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
-- splitOrAnt (NotBxA (Nbox n (ConBxA f g))) = map (NotBxA . boxJoin n) (splitOrAnt (NotBxA (ConBxA (NotBxA f) (NotBxA g))))
splitOrAnt (NotBxA (Nbox n (ConBxA f g))) = map (NotBxA . boxJoin n . NotBxA) (splitOrAnt (NotBxA (ConBxA f g)))
splitOrAnt (NotBxA (Nbox n (NotBxA f))) =  map (NotBxA . boxJoin n . NotBxA) (splitOrAnt f)
splitOrAnt (Nbox n f) = map (boxJoin n) (splitOrAnt f)
splitOrAnt (ConBxA f g) = [ConBxA f1 g1 | f1<- splitOrAnt f, g1<- splitOrAnt g]
splitOrAnt (NotBxA f) = map NotBxA (splitOrAnt f)
splitOrAnt f = [f]

-- (splitOrAnt (toModBxA (modSimp (dia (dis (Con (Prp 0) (dia (Prp 0))) (Not (Prp 1)))))))


-- ensure boxed atoms are joined (i.e. Nbox n (Nbox k _) does NOT occur)
boxJoin :: Int -> ModFormBxA -> ModFormBxA
boxJoin n (Nbox m f) = Nbox (n+m) f
boxJoin n (NotBxA (NotBxA f)) = boxJoin n f
boxJoin n f = Nbox n f

{-  
    functions to get FOL corr. of conj/disj of Sq formulas
-}
-- get FO corr. of disj. of Sq formulas 
-- NOTE: if multiple disjunctions will give Disjc lists in Disjc lists -> ugly -- TO DO
getFOLdisj :: ModFormBxA -> ModFormBxA -> FOLFormVSAnt -- f | g both Sq
getFOLdisj f g = Disjc [fromJust (getSqBxA f), 
    varsSub ((varsInFOLform2 (fromJust (getSqBxA f)) `intersect` varsInFOLform2 (fromJust (getSqBxA f))) \\ [0])
        (getNthFresh (length ((varsInFOLform2 (fromJust (getSqBxA f)) `intersect` varsInFOLform2 (fromJust (getSqBxA f)))\\[0])) (varsInFOLform2 (fromJust (getSqBxA f)) ++ varsInFOLform2 (fromJust (getSqBxA g))))
        (fromJust (getSqBxA g))]

getAllDisjs :: [ModFormBxA] -> [FOLFormVSAnt] -> [FOLFormVSAnt]
getAllDisjs ((NotBxA (ConBxA f g)):fs) gs 
    | isSqBxA (NotBxA f) && isSqBxA (NotBxA g) &&  null (props f `intersect` props g)
        = getAllDisjs fs (gs ++ [fromJust (getSqBxA f),fromJust (getSqBxA g)])
    | otherwise = getAllDisjs fs (gs ++ [fromJust (getSqBxA (NotBxA (ConBxA f g)))])
getAllDisjs (f:fs) gs = getAllDisjs fs (gs ++ [fromJust (getSqBxA f)])
getAllDisjs [] gs = gs

-- get FO corr. of conj. of Sq formulas
-- Same note about lists in lists
getFOLconj :: ModFormBxA -> ModFormBxA -> FOLFormVSAnt -- f & g both Sq
-- getFOLconj f g = Conjc [fromJust (getSqBxA f), fromJust (getSqBxA g)]
getFOLconj f g = Conjc [fromJust (getSqBxA f), 
    varsSub ((varsInFOLform2 (fromJust (getSqBxA f)) `intersect` varsInFOLform2 (fromJust (getSqBxA f))) \\ [0])
        (getNthFresh (length ((varsInFOLform2 (fromJust (getSqBxA f)) `intersect` varsInFOLform2 (fromJust (getSqBxA f)))\\[0])) (varsInFOLform2 (fromJust (getSqBxA f)) ++ varsInFOLform2 (fromJust (getSqBxA g))))
        (fromJust (getSqBxA g))]

{-
    functions to get FOL corr. of boxed Sq formulas 
-}

-- Get Sq ant of BOXES(Sq formula)
-- functionally same as normal getSqBxA, but keeps track of variables
getSqBxAbox :: ModFormBxA -> Int -> [Int] -> FOLFormVSAnt
getSqBxAbox TopBxA _ _ = Topc
getSqBxAbox (NotBxA TopBxA) _ _ = Negc Topc
getSqBxAbox (PrpBxA _) _ _ = Negc Topc -- p = T -> p
getSqBxAbox (NotBxA (NotBxA f)) x vars = getSqBxAbox f x vars
getSqBxAbox (NotBxA (ConBxA f g)) x vars |
    isSqAntBxA f && isNegativeBxA g =  varsSub -- f -> ~g
        (varsInFOLform2 (getFOLimp f (NotBxA g)) \\ [x])
        (getNthFresh (length (varsInFOLform2 (getFOLimp f (NotBxA g))) - 1) vars)
        (getFOLimp f (NotBxA g))
    | isSqAntBxA g && isNegativeBxA f =  varsSub -- g -> ~f
        (varsInFOLform2 (getFOLimp g (NotBxA f)) \\ [x])
        (getNthFresh (length (varsInFOLform2 (getFOLimp g (NotBxA f))) - 1) vars)
        (getFOLimp g (NotBxA f)) 
    | isSqBxA (NotBxA f) && isSqBxA (NotBxA g) &&  null (props f `intersect` props g) = -- ~(~f & ~g) both Sq + no shared props
            varsSub 
            (varsInFOLform2 (getFOLdisj (NotBxA f) (NotBxA g)) \\ [x])
            (getNthFresh (length (varsInFOLform2 (getFOLdisj (NotBxA f) (NotBxA g)))) vars)
            (getFOLdisj (NotBxA f) (NotBxA g))
getSqBxAbox (ConBxA f g) x vars | 
    isSqBxA f && isSqBxA g =
            varsSub 
            (varsInFOLform2 (getFOLconj f g) \\ [x])
            (getNthFresh (length (varsInFOLform2 (getFOLconj f g))) vars)
            (getFOLconj f g)
getSqBxAbox (Nbox n f) x vars | isSqBxA f = getFOLboxed1 n f x vars
getSqBxAbox f _ _ | isSqAntBxA (NotBxA f) =  getFOLimp (NotBxA f) (NotBxA TopBxA)
                    | isUniform f = getFOLuniform f

                -- -- | isNegativeBxA (NotBxA f) = getFOLuniform f

-- getSqBxAbox f | isSqAntBxA (NotBxA f) = Just (getFOLimp (NotBxA f) (NotBxA TopBxA))
--         | isNegativeBxA (NotBxA f) = Just (getFOLuniform f)
-- getSqBxAbox f _ _| isNegativeBxA f = getFOLmonoNeg f
--             | isNegativeBxA (NotBxA f) = getFOLimp TopBxA f
getSqBxAbox _ _ _= undefined

-- with Boxed At translation
getFOLboxed1 :: Int -> ModFormBxA -> Int -> [Int] -> FOLFormVSAnt
getFOLboxed1 n f x vars = (\y -> Forallc [V y] 
    (Impc (boxedR n vars x y) 
        (varsSub [x] [y] (getSqBxAbox f x (vars ++ getNthFresh n vars))))) (last (getNthFresh n vars))

-- on first call at variable x (V 0)
getFOLboxed :: Int -> ModFormBxA -> FOLFormVSAnt
getFOLboxed n f = getFOLboxed1 n f 0 [0]