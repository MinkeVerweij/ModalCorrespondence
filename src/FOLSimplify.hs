module FOLSimplify where

import Languages
import Data.List
import Data.Maybe
-- import FOLCorrespondent

-- STILL TO DO: take step back, simplify until no changes
simpFOL :: FOLFormVSAnt -> FOLFormVSAnt
simpFOL (Negc (Negc f)) = simpFOL f
simpFOL (Negc f) = Negc (simpFOL f)
simpFOL (Eqdotc t1 t2) | t1 == t2 = Topc
simpFOL (Conjc []) = Topc
simpFOL (Conjc [f]) = simpFOL f
simpFOL (Conjc fs) | Negc Topc `elem` fs = Negc Topc
                    | Topc `elem` fs = simpFOL (Conjc (fs \\ [Topc]))
                    | otherwise = Conjc (map simpFOL fs)
simpFOL (Disjc []) = Negc Topc
simpFOL (Disjc [f]) = simpFOL f
simpFOL (Disjc fs) | Topc `elem` fs = Topc
                | Negc Topc `elem` fs = simpFOL (Disjc (fs \\ [Negc Topc]))
                | otherwise = Disjc (map simpFOL fs)

simpFOL (Impc Topc g) = simpFOL g
simpFOL (Impc (Negc Topc) _) = Topc
simpFOL (Impc _ Topc) = Topc
simpFOL (Impc f (Negc Topc)) = simpFOL (Negc f)
simpFOL (Impc f g) = Impc (simpFOL f) (simpFOL g)

simpFOL (Forallc [] f) = simpFOL f
simpFOL (Forallc xs f) = remUnusedQuantVar (Forallc xs (simpFOL f))

simpFOL (Existsc [] f) = simpFOL f
simpFOL (Existsc xs f) = remUnusedQuantVar (Existsc xs (simpFOL f))

simpFOL f = f

simpFOL1 :: FOLFormVSAnt -> FOLFormVSAnt
simpFOL1 f | simpFOL f == f = f 
            | otherwise = simpFOL1 (simpFOL f)

simpExAND :: FOLFormVSAnt -> FOLFormVSAnt
simpExAND (Existsc xs (Conjc fs)) = simpFOL1 (exANDVarEq xs fs xs)
simpExAND (Forallc v f) = Forallc v (simpExAND f)
simpExAND (Conjc fs) = Conjc (map simpExAND fs)
simpExAND (Disjc fs) = Disjc (map simpExAND fs)
simpExAND (Impc f g) = Impc (simpExAND f) (simpExAND g)
simpExAND (Negc f) = Negc (simpExAND f)
simpExAND f = f

simpFOL2 :: FOLFormVSAnt -> FOLFormVSAnt
simpFOL2 f | simpExAND f == f = f
        | otherwise = simpFOL1 (simpExAND f)

simpFOL3 :: FOLFormVSAnt -> FOLFormVSAnt
simpFOL3 f = simpFOL2 (simpFOL1 f)

remUnusedQuantVar :: FOLFormVSAnt -> FOLFormVSAnt
remUnusedQuantVar (Existsc vars f) = Existsc (filter (`varInForm` f) vars) f
remUnusedQuantVar (Forallc vars f) = Forallc (filter (`varInForm` f) vars) f
remUnusedQuantVar f = f

varInForm :: Var -> FOLFormVSAnt -> Bool
varInForm _ Topc = False
varInForm x (Pc _ (VT y)) | x == y = True
                        |otherwise = False
varInForm _ (Pc _ _) = False
varInForm x (Rc (VT y) (VT z)) | x == y || x == z = True
                        | otherwise = False
varInForm _ (Rc _ _) = False
-- varInForm x (Rc _ (VT y)) | x == y = True
-- varInForm x (Rc (VT y) _) | x == y = True
varInForm x (Eqdotc (VT y) (VT z)) | x == y || x == z = True
                        | otherwise = False

varInForm _ (Eqdotc _ _) = False
-- varInForm x (Eqdotc (VT y) _) | x == y = True
-- varInForm x (Eqdotc _ (VT y)) | x == y = True
varInForm x (Negc f) = varInForm x f
varInForm x (Impc f g) = varInForm x f || varInForm x g
varInForm x (Disjc fs) = or [varInForm x f | f <- fs]
varInForm x (Conjc fs) = or [varInForm x f | f <- fs]
varInForm x (Existsc _ f) = varInForm x f
varInForm x (Forallc _ f) = varInForm x f



getEqVar :: Int -> [FOLFormVSAnt] -> Maybe Int
getEqVar x ((Eqdotc (VT (V i)) (VT (V j))):fs) 
                                    | i == x = Just j
                                    | j == x = Just i
                                    | otherwise = getEqVar x fs
getEqVar x (_:fs) = getEqVar x fs
getEqVar _ [] = Nothing

-- getEqVar 2 [Rc (VT (V 1)) (VT (V 2)), Eqdotc (VT (V 1)) (VT (V 2))]
-- exANDVarEq [V 2, V 3] [Rc (VT (V 1)) (VT (V 2)), Eqdotc (VT (V 1)) (VT (V 2))]
-- simpFOL (Existsc [V 2] (Conjc [Rc (VT (V 1)) (VT (V 2)),Eqdotc (VT (V 1)) (VT (V 2))]))
--  simpFOL1 (Forallc [V 1] (Impc (Rc (VT (V 0)) (VT (V 1))) (Existsc [V 2] (Conjc [Rc (VT (V 1)) (VT (V 2)),Eqdotc (VT (V 1)) (VT (V 2))]))))


-- simpExAND (Existsc [V 2,V 3] (Conjc [Rc (VT (V 0)) (VT (V 2)),Rc (VT (V 2)) (VT (V 3)),Eqdotc (VT (V 1)) (VT (V 3))]))
-- exANDVarEq [V 2, V 3] [Rc (VT (V 0)) (VT (V 2)),Rc (VT (V 2)) (VT (V 3)),Eqdotc (VT (V 1)) (VT (V 3))] [V 2, V 3]
exANDVarEq :: [Var] -> [FOLFormVSAnt] -> [Var] -> FOLFormVSAnt
exANDVarEq (V x:xs) fs allv | isJust (getEqVar x fs) = 
        remUnusedQuantVar (Existsc allv (Conjc [varsSub [x] [fromJust (getEqVar x fs)] f | f <- fs]))
            | otherwise = exANDVarEq xs fs allv

exANDVarEq [] fs allv = Existsc allv (simpFOL (Conjc fs))


-- subsitute [x0, x1, ..., xn] in FOL formula with [y0, y1, ..., yn]
varsSub :: [Int] -> [Int] -> FOLFormVSAnt -> FOLFormVSAnt
varsSub x y (Rc t1 t2)= Rc (varsSubTerm x y t1) (varsSubTerm x y t2)
varsSub x y (Eqdotc t1 t2)= Eqdotc (varsSubTerm x y t1) (varsSubTerm x y t2)
varsSub x y (Conjc fs) = Conjc [varsSub x y f| f <- fs]
varsSub x y (Disjc fs) = Disjc [varsSub x y f| f <- fs]
varsSub x y (Impc f g) = Impc (varsSub x y f) (varsSub x y g)
varsSub xs ys  (Forallc vars f) = Forallc 
    (map V (nub ((getInts vars \\ xs) ++ map (\x -> ys !! fromJust (elemIndex x xs)) (xs \\(xs \\ getInts vars)))))
    (varsSub xs ys f)
varsSub xs ys  (Existsc vars f) = Existsc 
    (map V (nub ((getInts vars \\ xs) ++ map (\x -> ys !! fromJust (elemIndex x xs)) (xs \\ (xs \\ getInts vars)))))
    (varsSub xs ys f)
varsSub x y (Negc f) = Negc (varsSub x y f)
varsSub _ _  Topc = Topc
varsSub x y (Pc k t) = Pc k (varsSubTerm x y t)

varsSubTerm :: [Int] -> [Int] -> Term -> Term
varsSubTerm  xs ys (VT (V i))| i `elem` xs = VT (V (ys !! fromJust (elemIndex i xs)))
                            | otherwise = VT (V i)
varsSubTerm _ _ t= t

getInts :: [Var] -> [Int]
getInts [] = []
getInts ((V x):xs) = x : getInts xs