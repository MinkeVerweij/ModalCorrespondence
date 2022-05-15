module FOLCorrespondent where
import Languages
import SQ_shape
import Stand_trans

-- import FOLSimplify
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
getSqBxA1 f | isJust (getSqBxA f) = Just (simpFOL (fromJust (getSqBxA f)))
            | otherwise = Nothing

getSqBxA :: ModFormBxA -> Maybe FOLFormVSAnt
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

getFOLmonoNeg :: ModFormBxA -> FOLFormVSAnt
getFOLmonoNeg f = standTransBxAmonoNeg f (V 0) [0]

getFOLimp :: ModFormBxA -> ModFormBxA -> FOLFormVSAnt -- f -> g Sq
getFOLimp f g | length (splitOrAnt f) == 1 = getFOLcorrNegAnt f g
            | otherwise = Conjc [getFOLcorrNegAnt fi g| fi <- splitOrAnt f]
-- getFOLimp f g | length (splitOrAnt f) == 1 = getFOLcorr (impBxA f g)
--             | otherwise = Conjc [getFOLcorr (impBxA fi g)| fi <- splitOrAnt f]

getFOLcorrNegAnt :: ModFormBxA -> ModFormBxA -> FOLFormVSAnt
getFOLcorrNegAnt f g | getPositiveBxA f /= f =
                        getFOLcorr (impBxA  (getPositiveBxA f) (disBxA (NotBxA (getNegativeBxA f)) g))
                    | otherwise = getFOLcorr (impBxA f g)

getPositiveBxA :: ModFormBxA -> ModFormBxA
getPositiveBxA f | isNegativeBxA (NotBxA f) = f
                | isNegativeBxA f = TopBxA
getPositiveBxA (ConBxA f g) = boxModSimp (ConBxA (getPositiveBxA f) (getPositiveBxA g))
getPositiveBxA (Nbox n f) = boxModSimp (Nbox n (getPositiveBxA f))
-- getPositiveBxA (PrpBxA k) = PrpBxA k
getPositiveBxA (NotBxA (ConBxA f g)) = boxModSimp (NotBxA (ConBxA (getNegativeBxA f) (getNegativeBxA g)))
getPositiveBxA (NotBxA (Nbox n f)) = boxModSimp (NotBxA (Nbox n (getNegativeBxA f)))
getPositiveBxA _ = undefined

posT :: [ModFormBxA]
posT = [
    -- getPositiveBxA (ConBxA (PrpBxA 0) (NotBxA (PrpBxA 1)))
    -- getPositiveBxA (NotBxA (Nbox 2 (NotBxA (ConBxA (Nbox 2 (PrpBxA 0)) (NotBxA (PrpBxA 0)))))),
    -- getNegativeBxA (NotBxA (Nbox 2 (NotBxA (ConBxA (Nbox 2 (PrpBxA 0)) (NotBxA (PrpBxA 0))))))
    getPositiveBxA (ConBxA (PrpBxA 0) (nDia 1 (NotBxA (PrpBxA 0)))),
    getNegativeBxA (ConBxA (PrpBxA 0) (nDia 1 (NotBxA (PrpBxA 0))))


    ]

getNegativeBxA :: ModFormBxA -> ModFormBxA
getNegativeBxA f | isNegativeBxA f = f
                | isNegativeBxA (NotBxA f) = TopBxA
getNegativeBxA (ConBxA f g) = boxModSimp (ConBxA (getNegativeBxA f) (getNegativeBxA g))
getNegativeBxA (Nbox n f) = boxModSimp (Nbox n (getNegativeBxA f))
getNegativeBxA (NotBxA (ConBxA f g)) = boxModSimp (NotBxA (ConBxA (getPositiveBxA f) (getPositiveBxA g)))
getNegativeBxA (NotBxA (Nbox n f)) = boxModSimp (NotBxA (Nbox n (getPositiveBxA f)))
getNegativeBxA _ = undefined


disAntT :: [FOLFormVSAnt]
disAntT = [
    -- getFOLimp (disBxA (Nbox 1 (PrpBxA 0)) (nDia 2 (PrpBxA 0))) (PrpBxA 0)
    getFOLimp (NotBxA (ConBxA (NotBxA (Nbox 1 (PrpBxA 0))) (Nbox 2 (NotBxA (PrpBxA 0))))) (PrpBxA 0)
    ]

getFOLdisj :: ModFormBxA -> ModFormBxA -> FOLFormVSAnt -- f | g both Sq
-- getFOLdisj f g| isJust (getSqBxA f) && isJust (getSqBxA f)  = Disjc [fromJust (getSqBxA f), fromJust (getSqBxA g)]
getFOLdisj f g = Disjc [fromJust (getSqBxA f), fromJust (getSqBxA g)]

getFOLconj :: ModFormBxA -> ModFormBxA -> FOLFormVSAnt -- f & g both Sq
-- getFOLconj f g| isJust (getSqBxA f) && isJust (getSqBxA f)  = Conjc [fromJust (getSqBxA f), fromJust (getSqBxA g)]
getFOLconj f g = Conjc [fromJust (getSqBxA f), fromJust (getSqBxA g)]

int1 :: [Int]
-- int1 = varsInFOLform2 (getFOLimp (nDia 1 (PrpBxA 0)) (PrpBxA 0)) \\ [0]
int1 = getNthFresh (length (varsInFOLform2 (getFOLimp (nDia 1 (PrpBxA 0)) (PrpBxA 0))) - 1) (0 : varsInFOLform2 (getFOLimp (nDia 1 (PrpBxA 0)) (PrpBxA 0)))

getSqBxAbox :: ModFormBxA -> Int -> [Int] -> FOLFormVSAnt
getSqBxAbox TopBxA _ _ = Topc
getSqBxAbox (NotBxA TopBxA) _ _ = Negc Topc
getSqBxAbox (PrpBxA _) _ _ = Negc Topc -- p = T -> p
getSqBxAbox (NotBxA (NotBxA f)) x vars = getSqBxAbox f x vars
getSqBxAbox (NotBxA (ConBxA f g)) x vars |
    isSqAntBxA f && isNegativeBxA g =  varsSub 
        (getFOLimp f (NotBxA g)) 
        (varsInFOLform2 (getFOLimp f (NotBxA g)) \\ [x])
        (getNthFresh (length (varsInFOLform2 (getFOLimp f (NotBxA g))) - 1) vars)-- f -> ~g
    | isSqAntBxA g && isNegativeBxA f =  varsSub 
        (getFOLimp g (NotBxA f)) 
        (varsInFOLform2 (getFOLimp g (NotBxA f)) \\ [x])
        (getNthFresh (length (varsInFOLform2 (getFOLimp g (NotBxA f))) - 1) vars)-- g -> ~f
    | isSqBxA (NotBxA f) && isSqBxA (NotBxA g) &&  null (props f `intersect` props g) = -- ~(~f & ~g) both Sq + no shared props
            varsSub (getFOLdisj (NotBxA f) (NotBxA g))
            (varsInFOLform2 (getFOLdisj (NotBxA f) (NotBxA g)) \\ [x])
            (getNthFresh (length (varsInFOLform2 (getFOLdisj (NotBxA f) (NotBxA g)))) vars)
--     | isSqAntBxA g && isNegativeBxA f =  Just (getFOLimp g (NotBxA f))-- g -> ~f
--     | isSqBxA (NotBxA f) && isSqBxA (NotBxA g) &&  null (props f `intersect` props g) = -- ~(~f & ~g) both Sq + no shared props
--             Just (getFOLdisj f g)
getSqBxAbox (ConBxA f g) x vars | 
    isSqBxA f && isSqBxA g =
            varsSub (getFOLconj f g)
            (varsInFOLform2 (getFOLconj f g) \\ [x])
            (getNthFresh (length (varsInFOLform2 (getFOLconj f g))) vars)
getSqBxAbox (Nbox n f) x vars | isSqBxA f = getFOLboxed1 n f x vars
getSqBxAbox _ _ _= undefined


test1 :: [FOLFormVSAnt]
test1 = [
    -- getSqBxAbox (Nbox 2 (impBxA (nDia 1 (PrpBxA 0)) (PrpBxA 0))) 0 [0]
    -- getSqBxAbox (impBxA (nDia 1 (PrpBxA 0)) (PrpBxA 0)) 0 [0]
    getSqBxAbox (impBxA (nDia 2 (PrpBxA 1)) (PrpBxA 1)) 0 [0]
    ]
getFOLboxed1 :: Int -> ModFormBxA -> Int -> [Int] -> FOLFormVSAnt
getFOLboxed1 n f x vars = (\y -> Forallc [V y] 
    (Impc (boxedR n vars x y) 
        (varSub (getSqBxAbox f x (vars ++ getNthFresh n vars)) x y ))) (last (getNthFresh n vars))

getFOLboxed :: Int -> ModFormBxA -> FOLFormVSAnt
getFOLboxed n f = getFOLboxed1 n f 0 [0]
-- getFOLboxed n f = (\y -> Forallc [y] (Impc (boxedR n [0] 0 y) (fromJust (getSqBxA f)))
-- getFOLboxed n f = (\y -> Forallc (varsInFOLform2 (fromJust (getSqBxA f))) FOLFormVSAnt)
-- getFOLboxed n f = (\fFOL -> standTransBxAvX (Nbox n fFOL)) (fromJust (getSqBxA f))

-- getFOLboxed n f = (\y -> Forallc [V y] 
--     (Impc (boxedR n [0] 0 y) 
--         (varSub (fromJust (getSqBxA f)) 0 y ))) (last (getNthFresh n [0]))

-- getFOLboxed n f = (\y -> Forallc [V y] 
--     (Impc (boxedR n [0] 0 y) 
--         (varSub (fromJust (getSqBxA f)) 0 y ))) (last (getNthFresh n [0]))
-- getFOLboxed = undefined

getInts :: [Var] -> [Int]
getInts [] = []
getInts ((V x):xs) = x : getInts xs

-- map (ys !! fromJust (elemIndex y xs (xs \\ vars) FOLFormVSAnt

-- map (\x -> ys !! fromJust (elemIndex x xs)) (xs \\ vars) 
-- int :: [Int]
-- int = map (\x -> [2] !! fromJust (elemIndex x [0,1])) ([1] \\ [0,1]) 


varsSub :: FOLFormVSAnt -> [Int] -> [Int] -> FOLFormVSAnt
varsSub (Rc t1 t2) x y = Rc (varsSubTerm t1 x y) (varsSubTerm t2 x y)
varsSub (Eqdotc t1 t2) x y = Eqdotc (varsSubTerm t1 x y) (varsSubTerm t2 x y)
varsSub (Conjc fs) x y= Conjc [varsSub f x y| f <- fs]
varsSub (Disjc fs) x y= Disjc [varsSub f x y| f <- fs]
varsSub (Impc f g) x y= Impc (varsSub f x y) (varsSub g x y)
varsSub (Forallc vars f) xs ys = Forallc 

    (map V (nub ((getInts vars \\ xs) ++ map (\x -> ys !! fromJust (elemIndex x xs)) (xs \\(xs \\ getInts vars)))))
    -- (map V ((getInts vars \\ xs) ++ ys))
    (varsSub f xs ys)
varsSub (Existsc vars f) xs ys = Existsc 
    (map V (nub ((getInts vars \\ xs) ++ map (\x -> ys !! fromJust (elemIndex x xs)) (xs \\ (xs \\ getInts vars)))))
    (varsSub f xs ys)
varsSub (Negc f) x y = Negc (varsSub f x y)
varsSub Topc _ _ = Topc
varsSub (Pc k t) x y = Pc k (varsSubTerm t x y)


-- (map V (nub ((getInts [V 0] \\ ([0] \\ [0])) ++ map (\x ->  !! fromJust (elemIndex x xs)) (xs \\ getInts vars))))
-- V x `elem` vars = Forallc (V y :(vars \\ [V x])) (varSub f x y)
--                             | otherwise = Forallc vars (varSub f x y)
-- varSub (Existsc vars f) x y | V x `elem` vars = Existsc (V y :(vars \\ [V x])) (varSub f x y)
--                             | otherwise = Existsc vars (varSub f x y)
-- varSub (Negc f) x y = Negc (varSub f x y)
-- varSub Topc _ _ = Topc
-- varSub (Pc k t) x y = Pc k (varSubTerm t x y)

varsSubTerm :: Term -> [Int] -> [Int] -> Term
varsSubTerm (VT (V i)) xs ys | i `elem` xs = VT (V (ys !! fromJust (elemIndex i xs)))
                            | otherwise = VT (V i)
varsSubTerm t _ _= t

varSub :: FOLFormVSAnt -> Int -> Int -> FOLFormVSAnt --replace x by y
varSub (Rc t1 t2) x y = Rc (varSubTerm t1 x y) (varSubTerm t2 x y)
varSub (Eqdotc t1 t2) x y = Eqdotc (varSubTerm t1 x y) (varSubTerm t2 x y)
varSub (Conjc fs) x y= Conjc [varSub f x y| f <- fs]
varSub (Disjc fs) x y= Disjc [varSub f x y| f <- fs]
varSub (Impc f g) x y= Impc (varSub f x y) (varSub g x y)
varSub (Forallc vars f) x y | V x `elem` vars = Forallc (V y :(vars \\ [V x])) (varSub f x y)
                            | otherwise = Forallc vars (varSub f x y)
varSub (Existsc vars f) x y | V x `elem` vars = Existsc (V y :(vars \\ [V x])) (varSub f x y)
                            | otherwise = Existsc vars (varSub f x y)
varSub (Negc f) x y = Negc (varSub f x y)
varSub Topc _ _ = Topc
varSub (Pc k t) x y = Pc k (varSubTerm t x y)

varSubTerm :: Term -> Int -> Int -> Term
varSubTerm (VT (V i)) x y | i == x = VT (V y)
                            | otherwise = VT (V i)
varSubTerm t _ _= t


props :: ModFormBxA -> [Int]
props (PrpBxA k) = [k]
props (ConBxA f g) = props f ++ props g
props (NotBxA f) = props f
props (Nbox _ f) = props f
props _ = []


isSqAntBxA :: ModFormBxA -> Bool
isSqAntBxA TopBxA = True
isSqAntBxA (NotBxA TopBxA) = True
isSqAntBxA (PrpBxA _) = True 
isSqAntBxA (NotBxA (NotBxA f)) = isSqAntBxA f
-- isSqAntBxA (NotBxA (Box (Box f))) = isSqAntBxA (NotBxA f) -- ~[][] = <><>~
-- isSqAnt (Not (Box (Not f))) = isSqAntBxA f -- ~[]~ = <>
isSqAntBxA (NotBxA (Nbox _ (NotBxA f))) = isSqAntBxA f
isSqAntBxA (NotBxA (Nbox _ (ConBxA f g))) = isSqAntBxA (NotBxA f) && isSqAntBxA (NotBxA g)
isSqAntBxA (ConBxA f g) = isSqAntBxA f && isSqAntBxA g
isSqAntBxA (Nbox _ (PrpBxA _)) = True -- Boxed atoms
isSqAntBxA (NotBxA (ConBxA f g)) = isSqAntBxA (NotBxA f) && isSqAntBxA (NotBxA g)  -- disj
isSqAntBxA f | isNegativeBxA f = True
            | otherwise = False
-- isSqAntBxA _ = False

test11 :: [Bool]
test11 = 
    [
        isSqAntBxA (toModBxA (modSimp (dia (dis (Box (Prp 0)) (dia (dia (Prp 0)))))))
    ]

antT  :: [Bool]
antT = [
    -- isSqAntBxA (NotBxA (PrpBxA 0))
    -- isSqAntBxA (disBxA (PrpBxA 0) (NotBxA (PrpBxA 1)))
    -- isSqAntBxA (Nbox 2 (disBxA (NotBxA (PrpBxA 0)) (NotBxA (PrpBxA 1))))
    isSqAntBxA (toModBxA (modSimp (dia (dis (Box (Prp 0)) (dia (dia (Prp 0)))))))
    ]
-- isSqAnt (Box f) = isBoxAt f
-- isSqAntBxA _ = False -- S

-- isSqAntBxA (ConBxA (nDia 2 (disBxA (PrpBxA 0) (PrpBxA 1))) (Nbox 1 (PrpBxA 0)))

-- split the OR in antecedent to use ((f OR g) -> h) equiv ((f -> h) AND (g -> h))
splitOrAnt :: ModFormBxA -> [ModFormBxA]
-- splitOrAnt = undefined
-- splitOrAnt (NotBxA (ConBxA (NotBxA f) (NotBxA g))) = splitOrAnt f ++ splitOrAnt g
-- splitOrAnt (NotBxA (ConBxA (NotBxA f) (NotBxA g))) | isNegativeBxA f && isNegativeBxA g =
--                         splitOrAnt f ++ splitOrAnt g
splitOrAnt (NotBxA (ConBxA f g)) = splitOrAnt (NotBxA f) ++ splitOrAnt (NotBxA g)
-- splitOrAnt (NotBxA (ConBxA f g)) | isNegativeBxA (NotBxA f) && isNegativeBxA (NotBxA g) =
--              splitOrAnt (NotBxA f) ++ splitOrAnt (NotBxA g)

-- splitOrAnt (ConBxA f g) = splitOrAnt (NotBxA f) ++ splitOrAnt (NotBxA g)
-- splitOrAnt (NotBxA (Nbox n (ConBxA (NotBxA f) (NotBxA g)))) = map (Nbox n) (splitOrAnt (NotBxA (ConBxA (NotBxA f) (NotBxA g))))
-- splitOrAnt (NotBxA (Nbox n (ConBxA (NotBxA f) (NotBxA g)))) = map (NotBxA . Nbox n) (splitOrAnt (NotBxA (ConBxA (NotBxA f) (NotBxA g))))

splitOrAnt (NotBxA (Nbox n (ConBxA f g))) = map (NotBxA . boxJoin n) (splitOrAnt (NotBxA (ConBxA (NotBxA f) (NotBxA g))))
splitOrAnt (NotBxA (Nbox n (NotBxA f))) =  map (NotBxA . boxJoin n . NotBxA) (splitOrAnt f)
    --map (NotBxA . boxJoin n) (splitOrAnt (NotBxA f))
splitOrAnt (Nbox n f) = map (boxJoin n) (splitOrAnt f)
-- splitOrAnt (ConBxA (NotBxA f) (NotBxA g)) = map NotBxA (splitOrAnt f) ++ map NotBxA (splitOrAnt g)
splitOrAnt (ConBxA f g) = [ConBxA f1 g1 | f1<- splitOrAnt f, g1<- splitOrAnt g]
splitOrAnt (NotBxA (NotBxA f)) = splitOrAnt f
splitOrAnt (NotBxA f) = map NotBxA (splitOrAnt f)
splitOrAnt f = [f]

boxJoin :: Int -> ModFormBxA -> ModFormBxA
boxJoin n (Nbox m f) = Nbox (n+m) f
boxJoin n (NotBxA (NotBxA f)) = boxJoin n f
boxJoin n f = Nbox n f


-- map (Nbox 1) [PrpBxA 0,PrpBxA 1]
splitT :: [[ModFormBxA]]
splitT = [
    -- splitOrAnt (disBxA (PrpBxA 0) (PrpBxA 1)),
        -- splitOrAnt (ConBxA (disBxA (PrpBxA 0) (PrpBxA 1)) (disBxA (PrpBxA 2) (PrpBxA 3)))
        -- splitOrAnt (ConBxA (NotBxA (ConBxA (NotBxA (PrpBxA 0)) (NotBxA (PrpBxA 1)))) (NotBxA (ConBxA (NotBxA (PrpBxA 2)) (NotBxA (PrpBxA 3)))))
        -- splitOrAnt (nDia 2 (disBxA (PrpBxA 0) (PrpBxA 1))) -- not input after simplification
        -- splitOrAnt (NotBxA (Nbox 2 (ConBxA (NotBxA (PrpBxA 0)) (NotBxA (PrpBxA 1)))))
        -- splitOrAnt (NotBxA (Nbox 2 (NotBxA (ConBxA (PrpBxA 0) (PrpBxA 1)))))
        -- splitOrAnt (ConBxA (NotBxA (PrpBxA 0)) (NotBxA (PrpBxA 1)))
        -- splitOrAnt (NotBxA (ConBxA (NotBxA (Nbox 1 (PrpBxA 0))) (Nbox 2 (NotBxA (PrpBxA 0)))))
        splitOrAnt (toModBxA (modSimp (dis (dia (dia (Con (Box (Box (Prp 0))) (Not (Prp 1))))) (Prp 2))))
        -- [toModBxA (modSimp (dis (dia (dia (Con (Box (Box (Prp 0))) (Not (Prp 1))))) (Prp 2)))]
        -- splitOrAnt (toModBxA (modSimp (dia (dis (dia (dia (Prp 0))) (Not (Prp 1))))))
        -- [toModBxA (modSimp (dia (dis (dia (dia (Prp 0))) (Not (Prp 1)))))]
        -- splitOrAnt (toModBxA (modSimp (dia (dis (dia (dia (Prp 0))) (Box (Prp 1))))))

        ]

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
-- isNegative (Box f) = isNegativeBx f

getSqAntBxA :: ModFormBxA -> ModFormBxA -- has to been through Sq check (+ be imp)
getSqAntBxA (NotBxA (NotBxA f)) = getSqAntBxA f
getSqAntBxA (NotBxA (ConBxA f g)) | isSqAntBxA f && isNegativeBxA g = f -- f -> ~g
                        | isSqAntBxA g && isNegativeBxA f = g -- g -> ~f
                        | otherwise = undefined
getSqAntBxA _ = undefined 

getSqCsqBxA :: ModFormBxA -> ModFormBxA -- has to been through Sq check (+ be imp)
getSqCsqBxA (NotBxA (NotBxA f)) = getSqCsqBxA f
getSqCsqBxA (NotBxA (ConBxA f g)) | isSqAntBxA f && isNegativeBxA g = NotBxA g -- f -> ~g
                        | isSqAntBxA g && isNegativeBxA f = NotBxA f -- g -> ~f
                        | otherwise = undefined
getSqCsqBxA _ = undefined


addVarRels :: ([Var], [FOLFormVSAnt]) -> ([Var], [FOLFormVSAnt]) -> ([Var], [FOLFormVSAnt])
addVarRels (vs1, rs1) (vs2, rs2) = (nub vs1 ++ vs2, nub rs1 ++ rs2)

getDiaRels :: FOLFormVSAnt -> [Var] -> [FOLFormVSAnt] -> ([Var], [FOLFormVSAnt])
getDiaRels (Existsc vars f) diavar rels = addVarRels (vars, []) (getDiaRels f diavar rels)
getDiaRels (Conjc [f]) diavar rels = getDiaRels f diavar rels
getDiaRels (Conjc (x:xs)) diavar rels = addVarRels (getDiaRels x diavar rels) (getDiaRels (Conjc xs) diavar rels)
getDiaRels (Rc t1 t2) diavar rels = (diavar, nub(Rc t1 t2 : rels))
getDiaRels _ diavar rels = (diavar, rels)

-- h :: [FOLFormVSAnt ]
-- h = nub ([Topc] ++ [Topc])

-- addVarRelsAts :: ([Var], [FOLFormVSAnt], [FOLFormVSAnt]) -> ([Var], [FOLFormVSAnt], [FOLFormVSAnt ]) -> ([Var], [FOLFormVSAnt], [FOLFormVSAnt])
-- addVarRelsAts (vs1, rs1, as1) (vs2, rs2, as2) = (nub vs1 ++ vs2, nub rs1 ++ rs2, nub as1 ++ nub as2)

-- getDiaRelsAts :: FOLFormVSAnt -> [Var] -> [FOLFormVSAnt] -> [FOLFormVSAnt]  -> ([Var], [FOLFormVSAnt], [FOLFormVSAnt])
-- getDiaRelsAts (Existsc vars f) diavar rels ats = addVarRelsAts (vars, [], []) (getDiaRelsAts f diavar rels ats)
-- getDiaRelsAts (Conjc [f]) diavar rels ats = getDiaRelsAts f diavar rels ats
-- getDiaRelsAts (Conjc (x:xs)) diavar rels ats = addVarRelsAts 
--             (getDiaRelsAts x diavar rels ats) 
--             (getDiaRelsAts (Conjc xs) diavar rels ats)
-- getDiaRelsAts (Rc t1 t2) diavar rels ats = (diavar, Rc t1 t2 : rels, ats)
-- getDiaRelsAts (Pc k t) diavar rels ats = (diavar, rels, Pc k t : ats)
-- getDiaRelsAts _ diavar rels ats = (diavar, rels, ats) -- SIMPLE

-- input: Sq Antecedent (S)
-- output: diavars, REL, (Sub BoxAtom: k (P id), sigma(P_k))
pullDiamonds1 :: FOLFormVSAnt -> ([Var], [FOLFormVSAnt])
pullDiamonds1 f = getDiaRels f [] []
-- pullDiamonds1 :: ModFormBxA -> ([Var], [FOLFormVSAnt], [(Int, Int -> FOLFormVSAnt)])
-- pullDiamonds1 f = (fst (getDiaRels (fst (standTransBxAgBA f (V 0) [0] [])) [] []),
--         snd (getDiaRels (fst (standTransBxAgBA f (V 0) [0] [])) [] []),
--         snd (standTransBxAgBA f (V 0) [0] []))


-- getBoxAt :: [(Int, Int, Int -> FOLFormVSAnt)] -> [FOLFormVSAnt]
-- getBoxAt [(y, k, )]

-- getPullDsFOL :: ModFormBxA -> [Var] -> [FOLFormVSAnt] -> [(Int, Int -> FOLFormVSAnt)] -> (FOLFormVSAnt, [Int -> FOLFormVSAnt])
-- getPullDsFOL f diams rels = undefined 

-- getFOLTrans :: (FOLFormVSAnt, [(Int, Int -> FOLFormVSAnt)]) -> FOLFormVSAnt
-- getFOLTrans (f, _) = f
-- getBxAtTrans :: (FOLFormVSAnt, [(Int, Int -> FOLFormVSAnt)], [FOLFormVSAnt]) -> [FOLFormVSAnt]
-- getBxAtTrans (_,_,bxAtTr) = bxAtTr

stTrAnt :: ModFormBxA -> FOLFormVSAnt
stTrAnt f = fst (standTransBxAgBA (getSqAntBxA f) (V 0) [0] [])

subsAnt :: ModFormBxA  -> [(Int, Int -> FOLFormVSAnt)]
subsAnt f = snd (standTransBxAgBA (getSqAntBxA f) (V 0) [0] [])
-- stTrBxAts :: ModFormBxA -> [FOLFormVSAnt]
-- stTrBxAts f = getBxAtTrans (standTransBxAgBA (getSqAntBxA f) (V 0) [0] [])

-- pulls diamonds, does not show BOX-AT as always cancels upon instatiation
getPullDsFOL :: ModFormBxA -> FOLFormVSAnt
getPullDsFOL f = Forallc (fst (pullDiamonds1 (stTrAnt f))) 
    (Impc 
        (Conjc (snd (pullDiamonds1 (stTrAnt f)))) 
        (standTransBxA (getSqCsqBxA f) (V 0) (varsInFOLform2 (stTrAnt f)))
    )

vT :: [Int]
vT = varsInFOLform2 (stTrAnt (impBxA (ConBxA (nDia 2 (Nbox 2 (PrpBxA 0))) (ConBxA (nDia 1 (PrpBxA 1)) (Nbox 1 (PrpBxA 2))))
         (nDia 1 (disBxA (PrpBxA 0) (Nbox 2 (PrpBxA 1))))))
    

tT :: [FOLFormVSAnt]
tT = [
        standTransBxA (getSqCsqBxA (impBxA (ConBxA (nDia 2 (Nbox 2 (PrpBxA 0))) (ConBxA (nDia 1 (PrpBxA 1)) (Nbox 1 (PrpBxA 2))))
         (nDia 1 (disBxA (PrpBxA 0) (Nbox 2 (PrpBxA 1)))))) (V 0) vT
    ]

pullDsT :: [FOLFormVSAnt]
pullDsT = [
    -- getPullDsFOL (impBxA (nDia 2 (ConBxA (nDia 1 (PrpBxA 1)) (Nbox 2 (PrpBxA 0)))) (Nbox 1 (PrpBxA 0)))
    getPullDsFOL (disBxA (NotBxA (nDia 3 (PrpBxA 0))) (nDia 1 (PrpBxA 0)))
    ]

instantiate1 :: FOLFormVSAnt -> [(Int, Int -> FOLFormVSAnt)] -> FOLFormVSAnt
instantiate1 (Pc k (VT (V x))) subs | not (null (minimalInst k subs)) =  getSubstitution k subs x
        | otherwise = Negc (Eqdotc (VT (V x)) (VT (V x)))
instantiate1 (Rc t1 t2) _ = Rc t1 t2
instantiate1 (Eqdotc t1 t2) _ = Eqdotc t1 t2
instantiate1 (Negc f) subs = Negc (instantiate1 f subs)
-- instantiate1 (Conjc fs) subs = Conjc (map (\f -> instantiate1 f subs) fs)
instantiate1 (Conjc fs) subs = Conjc (map (`instantiate1` subs) fs)
instantiate1 (Disjc fs) subs = Disjc (map (`instantiate1` subs) fs)
instantiate1 (Impc f g) subs = Impc f (instantiate1 g subs)
instantiate1 (Forallc vars f) subs = Forallc vars (instantiate1 f subs)
instantiate1 (Existsc vars f) subs = Existsc vars (instantiate1 f subs)
instantiate1 Topc _ = Topc
instantiate1 _ _ = undefined 


minimalInst :: Int -> [(Int, Int -> FOLFormVSAnt)] -> [Int -> FOLFormVSAnt]
minimalInst k subs = map snd $ filter ((==k) . fst) subs


--minimalInst _ [] = []
--minimalInst k [(j, subj)] | k == j = [subj]
--                                | otherwise = []
--minimalInst k ((j, subj):xs) | k == j = subj : minimalInst k xs
--                                | otherwise = minimalInst k xs

getNext:: [Int -> FOLFormVSAnt] -> (Int -> [FOLFormVSAnt])
getNext [] _ = []
getNext [x] y = [x y]
getNext (x:xs) y = x y : getNext xs y

bigDisj :: [Int -> FOLFormVSAnt] -> (Int -> FOLFormVSAnt)
bigDisj [x] y = x y
bigDisj (x:xs) y = Disjc (x y : getNext xs y)
bigDisj [] _ = undefined

getSubstitution :: Int -> [(Int, Int -> FOLFormVSAnt)] -> (Int -> FOLFormVSAnt)
getSubstitution k subs y = Disjc [ f y | f <- minimalInst k subs ]
    -- Disjc $ map ($ y) $ minimalInst k subs --bigDisj (minimalInst k subs)

getSubT :: [FOLFormVSAnt]
getSubT = [
    getSubstitution 0 (subsAnt (impBxA (ConBxA (Nbox 2 (PrpBxA 0)) (PrpBxA 0)) (nDia 1 (PrpBxA  0)))) 3
    ]

m1 :: [FOLFormVSAnt]
m1 = [bigDisj (minimalInst 0 [(0, boxedR 1 [0] 0), (1, boxedR 2 [0,1] 0), (0, boxedR 0 [0,1,2,3,4] 4)]) 8]
-- m = Disjc (map (minimalInst 0 [(0, boxedR 1 [0] 0)]))

-- getSubst :: [Int -> FOLFormVSAnt] -> (Int -> FOLFormVSAnt)
-- getSubst minInst = Disjc minInst

-- input :: Sq impl (S)
-- output :: FOL correspondent (unsimplified)
getFOLcorr :: ModFormBxA -> FOLFormVSAnt
getFOLcorr f = instantiate1 (getPullDsFOL f) (subsAnt f)

simSqT :: [FOLFormVSAnt]
simSqT = [
    -- getFOLcorr (impBxA (nDia 2 (PrpBxA 0)) (nDia 1 (PrpBxA 0)))
    getFOLcorr (impBxA (ConBxA (Nbox 2 (PrpBxA 0)) (PrpBxA 0)) (nDia 1 (PrpBxA  0)))

    -- getFOLcorr (impBxA (ConBxA (nDia 2 (disBxA (PrpBxA 0) (PrpBxA 1))) (Nbox 1 (PrpBxA 0))) (PrpBxA 0))
    -- getFOLcorr (impBxA (Nbox 2 (PrpBxA 0)) (Nbox 3 (PrpBxA 0)))
    -- getFOLcorr (impBxA (PrpBxA 0) (nDia 1 (PrpBxA 0)))
    -- getFOLcorr (impBxA (nDia 1 (PrpBxA 0)) (nDia 2 (PrpBxA 0)))
    -- getFOLcorr (impBxA (ConBxA (PrpBxA 0) (nDia 2 (PrpBxA 0))) (nDia 1 (PrpBxA 0)))
    -- getFOLcorr (impBxA (PrpBxA 0) (PrpBxA 1))
    -- getFOLcorr (impBxA TopBxA (nDia 1 (Nbox 1 (PrpBxA 0))))
    -- getFOLcorr (disBxA (NotBxA (nDia 3 (PrpBxA 0))) (nDia 2 (PrpBxA 0)))
    -- getFOLcorr (impBxA (ConBxA (nDia 2 (Nbox 2 (PrpBxA 0))) (ConBxA (nDia 1 (PrpBxA 1)) (Nbox 1 (PrpBxA 2))))
    --      (nDia 1 (disBxA (PrpBxA 0) (Nbox 2 (PrpBxA 1)))))
    -- getFOLcorr (disBxA (disBxA (NotBxA (PrpBxA 0)) (NotBxA (nDia 2 (PrpBxA 0)))) (nDia 1 (PrpBxA 0)))
    ]