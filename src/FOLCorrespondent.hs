module FOLCorrespondent where
import Languages
import StandTrans
import Data.List
import Data.Maybe
import ModalSimplify
import FOLSimplify

isSqBxA :: ModFormBxA -> Bool
isSqBxA TopBxA = True
isSqBxA (NotBxA TopBxA) = True
isSqBxA (PrpBxA _) = True -- p = T -> p
isSqBxA (NotBxA (NotBxA f)) = isSqBxA f
isSqBxA (NotBxA (ConBxA f g)) = 
    isSqAntBxA f && isNegativeBxA g || -- f -> ~g
    isSqAntBxA g && isNegativeBxA f || -- g -> ~f
    isSqBxA (NotBxA f) && isSqBxA (NotBxA g) &&  null (props f `intersect` props g) -- ~(~f & ~g) both Sq + no shared props
isSqBxA (ConBxA f g) = isSqBxA f && isSqBxA g
isSqBxA (Nbox _ f) = isSqBxA f
isSqBxA _ = False

getSqBxA1 :: ModFormBxA -> Maybe FOLFormVSAnt
getSqBxA1 f | isJust (getSqBxA f) = Just (simpFOL1 (fromJust (getSqBxA f)))
            | otherwise = Nothing

getSqBxA :: ModFormBxA -- ^ returns Sq correspondent if any
  -> Maybe FOLFormVSAnt
getSqBxA TopBxA = Just Topc
getSqBxA (NotBxA TopBxA) = Just (Negc Topc)
getSqBxA (PrpBxA _) = Just (Negc Topc) -- p = T -> p
getSqBxA (NotBxA (PrpBxA _)) = Just (Negc Topc)
getSqBxA (NotBxA (NotBxA f)) = getSqBxA f
getSqBxA (NotBxA (ConBxA f g)) |
    isSqAntBxA f && isNegativeBxA g =  Just (getFOLimp f (NotBxA g))-- f -> ~g
    | isSqAntBxA g && isNegativeBxA f =  Just (getFOLimp g (NotBxA f))-- g -> ~f
    | isSqBxA (NotBxA f) && isSqBxA (NotBxA g) &&  null (props f `intersect` props g) = -- ~(~f & ~g) both Sq + no shared props
            Just (getFOLdisj (NotBxA f) (NotBxA g))
getSqBxA (ConBxA f g) | isSqBxA f && isSqBxA g = Just (getFOLconj f g)
getSqBxA (Nbox n f) | isSqBxA f = Just (getFOLboxed n f)
getSqBxA f | isNegativeBxA f = Just (getFOLmonoNeg f)
            | isNegativeBxA (NotBxA f) = Just (getFOLimp TopBxA f)
getSqBxA _ = Nothing

-- special case negative monotonic formulas (subst Px for x=x)
getFOLmonoNeg :: ModFormBxA -> FOLFormVSAnt
getFOLmonoNeg f = standTransBxAmonoNeg f (V 0) [0]

-- get FO corresp. for Sq implication, becomes multiple when OR in antecedent
getFOLimp :: ModFormBxA -> ModFormBxA -> FOLFormVSAnt -- f -> g Sq
getFOLimp f g | length (splitOrAnt f) == 1 = getFOLcorrNegAnt f g
            | otherwise = Conjc [getFOLcorrNegAnt fi g| fi <- splitOrAnt f]


-- move negative part of antecedent to consequent
getFOLcorrNegAnt :: ModFormBxA -> ModFormBxA -> FOLFormVSAnt
getFOLcorrNegAnt f g | getPositiveBxA f /= f =
                        getFOLcorr (impBxA  (getPositiveBxA f) (disBxA (NotBxA (getNegativeBxA f)) g))
                    | otherwise = getFOLcorr (impBxA f g)

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

-- get propositions from Modal Formula (for disj. Sq formulas)
props :: ModFormBxA -> [Int]
props (PrpBxA k) = [k]
props (ConBxA f g) = props f ++ props g
props (NotBxA f) = props f
props (Nbox _ f) = props f
props _ = []

-- get FO corr. of disj. of Sq formulas 
-- NOTE: if multiple disjunctions will give Disjc lists in Disjc lists -> ugly -- TO DO
getFOLdisj :: ModFormBxA -> ModFormBxA -> FOLFormVSAnt -- f | g both Sq
getFOLdisj f g = Disjc [fromJust (getSqBxA f), fromJust (getSqBxA g)]

-- get FO corr. of conj. of Sq formulas
-- Same note about lists in lists
getFOLconj :: ModFormBxA -> ModFormBxA -> FOLFormVSAnt -- f & g both Sq
getFOLconj f g = Conjc [fromJust (getSqBxA f), fromJust (getSqBxA g)]

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
getSqBxAbox _ _ _= undefined


-- with Boxed At translation
getFOLboxed1 :: Int -> ModFormBxA -> Int -> [Int] -> FOLFormVSAnt
getFOLboxed1 n f x vars = (\y -> Forallc [V y] 
    (Impc (boxedR n vars x y) 
        (varsSub [x] [y] (getSqBxAbox f x (vars ++ getNthFresh n vars))))) (last (getNthFresh n vars))

-- on first call at variable x (V 0)
getFOLboxed :: Int -> ModFormBxA -> FOLFormVSAnt
getFOLboxed n f = getFOLboxed1 n f 0 [0]


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

-- split the OR in antecedent to use ((f OR g) -> h) equiv ((f -> h) AND (g -> h))
splitOrAnt :: ModFormBxA -> [ModFormBxA]
splitOrAnt (NotBxA (ConBxA f g)) = splitOrAnt (NotBxA f) ++ splitOrAnt (NotBxA g)
splitOrAnt (NotBxA (Nbox n (ConBxA f g))) = map (NotBxA . boxJoin n) (splitOrAnt (NotBxA (ConBxA (NotBxA f) (NotBxA g))))
splitOrAnt (NotBxA (Nbox n (NotBxA f))) =  map (NotBxA . boxJoin n . NotBxA) (splitOrAnt f)
splitOrAnt (Nbox n f) = map (boxJoin n) (splitOrAnt f)
splitOrAnt (ConBxA f g) = [ConBxA f1 g1 | f1<- splitOrAnt f, g1<- splitOrAnt g]
splitOrAnt (NotBxA (NotBxA f)) = splitOrAnt f
splitOrAnt (NotBxA f) = map NotBxA (splitOrAnt f)
splitOrAnt f = [f]

-- ensure boxed atoms are joined (i.e. Nbox n (Nbox k _) does NOT occur)
boxJoin :: Int -> ModFormBxA -> ModFormBxA
boxJoin n (Nbox m f) = Nbox (n+m) f
boxJoin n (NotBxA (NotBxA f)) = boxJoin n f
boxJoin n f = Nbox n f

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

-- get (very) simple Sq antecedent (only called after preprocessing)
getSqAntBxA :: ModFormBxA -> ModFormBxA
getSqAntBxA (NotBxA (NotBxA f)) = getSqAntBxA f
getSqAntBxA (NotBxA (ConBxA f g)) | isSqAntBxA f && isNegativeBxA g = f -- f -> ~g
                        | isSqAntBxA g && isNegativeBxA f = g -- g -> ~f
                        | otherwise = undefined
getSqAntBxA _ = undefined 

-- get (very) simple Sq consequent (only called after preprocessing)
getSqCsqBxA :: ModFormBxA -> ModFormBxA
getSqCsqBxA (NotBxA (NotBxA f)) = getSqCsqBxA f
getSqCsqBxA (NotBxA (ConBxA f g)) | isSqAntBxA f && isNegativeBxA g = NotBxA g -- f -> ~g
                        | isSqAntBxA g && isNegativeBxA f = NotBxA f -- g -> ~f
                        | otherwise = undefined
getSqCsqBxA _ = undefined


-- get variables (diamonds to pull) and relations REL
getDiaRels :: FOLFormVSAnt -> [Var] -> [FOLFormVSAnt] -> ([Var], [FOLFormVSAnt])
getDiaRels (Existsc vars f) diavar rels = addVarRels (vars, []) (getDiaRels f diavar rels)
getDiaRels (Conjc [f]) diavar rels = getDiaRels f diavar rels
getDiaRels (Conjc (x:xs)) diavar rels = addVarRels (getDiaRels x diavar rels) (getDiaRels (Conjc xs) diavar rels)
getDiaRels (Rc t1 t2) diavar rels = (diavar, nub(Rc t1 t2 : rels))
getDiaRels _ diavar rels = (diavar, rels)

-- helper getDiaRels
addVarRels :: ([Var], [FOLFormVSAnt]) -> ([Var], [FOLFormVSAnt]) -> ([Var], [FOLFormVSAnt])
addVarRels (vs1, rs1) (vs2, rs2) = (nub vs1 ++ vs2, nub rs1 ++ rs2)

-- input: Sq Antecedent (S)
-- output: diavars, REL, (Sub BoxAtom: k (P id), sigma(P_k))
pullDiamonds1 :: FOLFormVSAnt -> ([Var], [FOLFormVSAnt])
pullDiamonds1 f = getDiaRels f [] []

-- standard translation of antecedent (at x)
stTrAnt :: ModFormBxA -> FOLFormVSAnt
stTrAnt f = fst (standTransBxAgBA (getSqAntBxA f) (V 0) [0] [])

-- substitution 'dictionary' of antecedent
-- get (Pred id int, substitution as function of variable id int)
subsAnt :: ModFormBxA  -> [(Int, Int -> FOLFormVSAnt)]
subsAnt f = snd (standTransBxAgBA (getSqAntBxA f) (V 0) [0] [])

-- get FO formula after pulling diamonds
getPullDsFOL :: ModFormBxA -> FOLFormVSAnt
getPullDsFOL f = Forallc (fst (pullDiamonds1 (stTrAnt f))) 
    (Impc 
        (Conjc (snd (pullDiamonds1 (stTrAnt f)))) 
        (standTransBxA (getSqCsqBxA f) (V 0) (varsInFOLform2 (stTrAnt f)))
    )

-- instantiate i.e. substitute predicates for minimal instances
instantiate1 :: FOLFormVSAnt -> [(Int, Int -> FOLFormVSAnt)] -> FOLFormVSAnt
instantiate1 (Pc k (VT (V x))) subs | not (null (minimalInst k subs)) =  getSubstitution k subs x
        | otherwise = Negc (Eqdotc (VT (V x)) (VT (V x)))
instantiate1 (Rc t1 t2) _ = Rc t1 t2
instantiate1 (Eqdotc t1 t2) _ = Eqdotc t1 t2
instantiate1 (Negc f) subs = Negc (instantiate1 f subs)
instantiate1 (Conjc fs) subs = Conjc (map (`instantiate1` subs) fs)
instantiate1 (Disjc fs) subs = Disjc (map (`instantiate1` subs) fs)
instantiate1 (Impc f g) subs = Impc f (instantiate1 g subs)
instantiate1 (Forallc vars f) subs = Forallc vars (instantiate1 f subs)
instantiate1 (Existsc vars f) subs = Existsc vars (instantiate1 f subs)
instantiate1 Topc _ = Topc
instantiate1 _ _ = undefined 

-- get minimal instances for every predicate
-- input: Pred. id, list of all possible substitutions [(pred id, subst(var))]
-- output: list of substitutions for given pred id
minimalInst :: Int -> [(Int, Int -> FOLFormVSAnt)] -> [Int -> FOLFormVSAnt]
minimalInst k subs = map snd $ filter ((==k) . fst) subs

-- makes disjunction over minimal instances provided a predicate (id)
-- output: disj. of all subst. of given predicate, s.t. 1 var can be applied
getSubstitution :: Int -> [(Int, Int -> FOLFormVSAnt)] -> (Int -> FOLFormVSAnt)
getSubstitution k subs y = Disjc [ f y | f <- minimalInst k subs ]

-- input :: Sq impl (S)
-- output :: FOL correspondent (unsimplified)
getFOLcorr :: ModFormBxA -> FOLFormVSAnt
getFOLcorr f = instantiate1 (getPullDsFOL f) (subsAnt f)