module FOLSimplify where

import Languages
import Data.List
import Data.Maybe
import Data.Bifunctor
{- Simplification of FOL formulas -}

-- general simplify first, then simplify 'Exists v_i (x=v_i & a(v_i))' to a(x)
simpFOL3 :: FOLFormVSAnt -> FOLFormVSAnt
simpFOL3 f = simpFOL5 (simpFOL2 (simpFOL1 f))

-- general simplification
simpFOL :: FOLFormVSAnt -> FOLFormVSAnt
simpFOL (Negc (Negc f)) = simpFOL f
simpFOL (Negc f) = Negc (simpFOL f)
simpFOL (Eqdotc t1 t2) | t1 == t2 = Topc
simpFOL (Conjc []) = Topc
simpFOL (Conjc [f]) = simpFOL f
simpFOL (Conjc fs) | Negc Topc `elem` fs = Negc Topc
                    | Topc `elem` fs = simpFOL (Conjc (nub (fs \\ [Topc])))
                    | otherwise = Conjc (flattenCon (map simpFOL (nub fs)))
simpFOL (Disjc []) = Negc Topc
simpFOL (Disjc [f]) = simpFOL f
simpFOL (Disjc fs) | Topc `elem` fs = Topc
                | Negc Topc `elem` fs = simpFOL (Disjc (nub (fs \\ [Negc Topc])))
                | otherwise = Disjc (flattenDis (map simpFOL (nub fs)))

simpFOL (Impc Topc g) = simpFOL g
simpFOL (Impc (Negc Topc) _) = Topc
simpFOL (Impc _ Topc) = Topc
simpFOL (Impc f (Negc Topc)) = simpFOL (Negc f)

simpFOL (Forallc vars (Impc f (Forallc vars2 (Impc g h)))) =  Forallc (vars ++ vars2) (simpFOL (Impc (Conjc (flattenCon [f, g])) h)) --Conjc [remUnusedQuantVar (simpFOL (Forallc vars (Impc f g))) | g <- gs]
-- simpFOL (Forallc vars (Impc f (Existsc vars2 (Conjc gs)))) = Existsc vars2 (Conjc [remUnusedQuantVar (simpFOL (Forallc vars (Impc f g))) | g <- gs])

simpFOL (Impc f g) = Impc (simpFOL f) (simpFOL g)

simpFOL (Forallc [] f) = simpFOL f
simpFOL (Forallc xs f) = remUnusedQuantVar (Forallc xs (simpFOL f))

simpFOL (Existsc [] f) = simpFOL f
simpFOL (Existsc xs f) = remUnusedQuantVar (Existsc xs (simpFOL f))

simpFOL f = f

-- continue general until no changes
simpFOL1 :: FOLFormVSAnt -> FOLFormVSAnt
simpFOL1 f | simpFOL f == f = f 
            | otherwise = simpFOL1 (simpFOL f)

flattenCon :: [FOLFormVSAnt] -> [FOLFormVSAnt]
flattenCon [] = []
flattenCon (Conjc fs:gs) = fs ++ flattenCon gs
flattenCon (f:fs) = f : flattenCon fs

flattenDis :: [FOLFormVSAnt] -> [FOLFormVSAnt]
flattenDis [] = []
flattenDis (Disjc fs:gs) = fs ++ flattenDis gs
flattenDis (f:fs) = f : flattenDis fs

hasforAllImp :: [FOLFormVSAnt] -> Bool
hasforAllImp [] = False
hasforAllImp ((Forallc _ (Impc _ _)):_) = True
hasforAllImp ((Existsc _ (Conjc fs)):rest) = hasforAllImp fs || hasforAllImp rest
hasforAllImp (_:fs) = hasforAllImp fs

hasForAll :: [FOLFormVSAnt] -> Bool
hasForAll [] = False
hasForAll ((Forallc _ _):_) = True
hasForAll (_:fs) = hasForAll fs

-- instantiate possible existentials and simplify again
simpFOL2 :: FOLFormVSAnt -> FOLFormVSAnt
simpFOL2 f | simpExAND f == f = f
        | otherwise = simpFOL1 (simpExAND f)

simpFOL4 :: FOLFormVSAnt -> FOLFormVSAnt
simpFOL4 (Negc (Conjc fs)) =  Disjc [simpFOL2 (simpFOL4 (simpFOL1 (Negc f)))|f<- fs]
simpFOL4 (Negc (Impc f g)) = Conjc [simpFOL1 f, simpFOL1 (Negc g)]
simpFOL4 (Negc (Existsc vars f)) = Forallc vars (simpFOL4 (simpFOL1 (Negc f)))
simpFOL4 (Negc (Forallc vars f)) = Existsc vars (simpFOL4 (simpFOL1 (Negc f)))
-- simpFOL4 (Forallc vars (Impc f (Forallc vars2 (Impc g h)))) =  Forallc (vars ++ vars2)  (Impc (Conjc (flattenCon [simpFOL4 f, simpFOL4 g])) h) 
-- simpFOL4 (Forallc vars (Impc f (Existsc vars2 (Conjc gs)))) | hasForAll gs = Existsc vars2 (Conjc [remUnusedQuantVar (simpFOL (Forallc vars (Impc f g))) | g <- gs])
-- simpFOL4 (Forallc vars (Impc f (Existsc vars2 (Disjc gs)))) | hasForAll gs = Existsc vars2 (Disjc [remUnusedQuantVar (simpFOL (Forallc vars (Impc f g))) | g <- gs])
simpFOL4 (Conjc fs) = Conjc [simpFOL4 f | f<- fs]
simpFOL4 (Disjc fs) = Disjc [simpFOL4 f | f<- fs]
simpFOL4 f = f

simpFOL5 :: FOLFormVSAnt -> FOLFormVSAnt
simpFOL5 f | simpFOL4 f == f = f
        | otherwise = simpFOL4 f

simpFOLViz :: FOLFormVSAnt -> FOLFormVSAnt
simpFOLViz (Forallc vars (Impc f (Forallc vars2 (Impc g h)))) = simpFOLViz (Forallc (vars ++ vars2)  (simpFOL1 (Impc (Conjc (flattenCon [f, g])) h)))
simpFOLViz (Forallc vars (Impc f (Existsc vars2 (Conjc gs)))) | hasForAll gs = Existsc vars2 (Conjc [simpFOLViz (Forallc vars (Impc f g)) | g <- gs])
simpFOLViz (Forallc vars (Impc f (Conjc gs))) = Conjc [simpFOLViz (Forallc vars (Impc f g)) | g <- gs]
simpFOLViz (Conjc fs) = Conjc (flattenCon [simpFOLViz f | f <- fs])
simpFOLViz (Disjc fs) | not (null (negForms fs)) && not (null (posForms fs)) = simpFOL1 (Impc (Conjc (negForms fs)) (Conjc (posForms fs)))
                    | otherwise = Disjc (flattenDis [simpFOLViz f | f <- fs])
simpFOLViz (Existsc vars (Conjc fs)) | not (null (snd (getVarsExForms fs))) = Existsc (vars ++ snd (getVarsExForms fs)) (Conjc (flattenCon (fst (getVarsExForms fs))))
                            | otherwise = Existsc vars (Conjc (flattenCon [simpFOLViz f | f <- fs]))
simpFOLViz (Existsc vars (Disjc fs)) = Existsc vars (Disjc (flattenDis [simpFOLViz f | f <- fs]))
-- simpFOLViz (Existsc vars f) = Existsc vars (simpFOLViz f)
simpFOLViz (Forallc vars f) = Forallc vars (simpFOLViz f)
simpFOLViz f = simpFOL1 f

getVarsExForms :: [FOLFormVSAnt] -> ([FOLFormVSAnt], [Var])
getVarsExForms [] = ([],[])
getVarsExForms ((Existsc vars f):fs) = bimap (f :) (vars ++) (getVarsExForms fs) -- (f : fst (getVarsExForms fs), vars ++ snd (getVarsExForms fs))
getVarsExForms (f:fs) = bimap (f :) ([] ++) (getVarsExForms fs)
-- getVarsExForms :: [FOLFormVSAnt] -> [Var] -> ([Var], [FOLFormVSAnt])
-- getVarsExForms ((Existsc vars f):fs) v = ((v ++ vars), [f]) ++ (getVarsExForms fs (v ++ vars))


simpFOLViz1 :: FOLFormVSAnt -> FOLFormVSAnt
simpFOLViz1 f | simpFOLViz f == f = f
            | otherwise = simpFOLViz f

simpFOLViz2 :: FOLFormVSAnt -> FOLFormVSAnt
simpFOLViz2 f | simpFOLViz1 (simpFOLViz1 f) == f = f
            | otherwise = simpFOLViz1 (simpFOLViz1 f)


{- instantiate possible existentials
    'Exists v_i (x=v_i & a(v_i))' => a(x)
        can also be ORs within AND, need to keep OR
-}
simpExAND :: FOLFormVSAnt -> FOLFormVSAnt
simpExAND (Existsc xs (Conjc fs)) 
    | Conjc fs == disjOuter (Conjc fs) fs = simpFOL1 (remUnusedQuantVar (Existsc xs (exANDVarEq xs fs)))
    | otherwise = simpFOL1 (remUnusedQuantVar 
        (Existsc xs (exORANDSVarEq1 xs 
            (map getDCjuncts (getDCjuncts (disjOuter (Conjc fs) fs))))))
simpExAND (Forallc v f) = Forallc v (simpExAND f)
simpExAND (Conjc fs) = Conjc (map simpExAND fs)
simpExAND (Disjc fs) = Disjc (map simpExAND fs)
simpExAND (Impc f g) = Impc (simpExAND f) (simpExAND g)
simpExAND (Negc f) = Negc (simpExAND f)
simpExAND f = f

-- Conjunction of dijunctions => disjunction of conjunctions
disjOuter :: FOLFormVSAnt -> [FOLFormVSAnt] -> FOLFormVSAnt
disjOuter (Conjc (Disjc gs:_)) hs = Disjc (map (\g -> Conjc (g: (hs \\ [Disjc gs]))) gs)
disjOuter (Conjc (_:fs)) hs = disjOuter (Conjc fs) hs
disjOuter (Conjc []) hs = Conjc hs
disjOuter _ _= undefined

getDCjuncts :: FOLFormVSAnt -> [FOLFormVSAnt]
getDCjuncts (Disjc fs) = fs
getDCjuncts (Conjc fs) = fs
getDCjuncts _ = undefined

-- Only quantify over variables that are in formula f (Qx f) 
remUnusedQuantVar :: FOLFormVSAnt -> FOLFormVSAnt
remUnusedQuantVar (Existsc vars f) = Existsc (filter (`varInForm` f) vars) f
remUnusedQuantVar (Forallc vars f) = Forallc (filter (`varInForm` f) vars) f
remUnusedQuantVar f = f

-- Exists (Conj fs) w/ fs has no disjuncts
exANDVarEq :: [Var] -> [FOLFormVSAnt] -> FOLFormVSAnt
exANDVarEq (V x:xs) fs | isJust (getEqVar x fs) = 
         simpFOL1 (Conjc [varsSub [x] [fromJust (getEqVar x fs)] f | f <- fs])
            | otherwise = exANDVarEq xs fs

exANDVarEq [] fs = simpExAND (simpFOL1 (Conjc fs))

-- Exists (Disj fs) w/ fs conjunctions
exORANDSVarEq1 :: [Var] -> [[FOLFormVSAnt]] -> FOLFormVSAnt
exORANDSVarEq1 vars fss = Disjc (exORANDSVarEq vars fss)

exORANDSVarEq :: [Var] -> [[FOLFormVSAnt]] -> [FOLFormVSAnt]
exORANDSVarEq vars = map (exANDVarEq vars)

-- get the variable that the quantified var is equal to, if any
getEqVar :: Int -> [FOLFormVSAnt] -> Maybe Int
getEqVar x ((Eqdotc (VT (V i)) (VT (V j))):fs) 
                                    | i == x = Just j
                                    | j == x = Just i
                                    | otherwise = getEqVar x fs
getEqVar x (_:fs) = getEqVar x fs
getEqVar _ [] = Nothing


{- 
    Helper functions to work with variables
-}
-- check whether a variable is in a formula
varInForm :: Var -> FOLFormVSAnt -> Bool
varInForm _ Topc = False
varInForm x (Pc _ (VT y)) | x == y = True
                        |otherwise = False
varInForm _ (Pc _ _) = False
varInForm x (Rc (VT y) (VT z)) | x == y || x == z = True
                        | otherwise = False
varInForm _ (Rc _ _) = False
varInForm x (Eqdotc (VT y) (VT z)) | x == y || x == z = True
                        | otherwise = False
varInForm _ (Eqdotc _ _) = False
varInForm x (Negc f) = varInForm x f
varInForm x (Impc f g) = varInForm x f || varInForm x g
varInForm x (Disjc fs) = or [varInForm x f | f <- fs]
varInForm x (Conjc fs) = or [varInForm x f | f <- fs]
varInForm x (Existsc _ f) = varInForm x f
varInForm x (Forallc _ f) = varInForm x f

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

-- substitute variables [x0,..,xn] in term with [y0,..,yn]
varsSubTerm :: [Int] -> [Int] -> Term -> Term
varsSubTerm  xs ys (VT (V i))| i `elem` xs = VT (V (ys !! fromJust (elemIndex i xs)))
                            | otherwise = VT (V i)
varsSubTerm _ _ t= t

getInts :: [Var] -> [Int]
getInts [] = []
getInts ((V x):xs) = x : getInts xs

posForms :: [FOLFormVSAnt] -> [FOLFormVSAnt]
posForms [] = []
posForms ((Negc _):fs) = posForms fs
posForms (f:fs) = f : posForms fs

negForms :: [FOLFormVSAnt] -> [FOLFormVSAnt]
negForms [] = []
negForms ((Negc f):fs) = f : negForms fs
negForms (_:fs) = negForms fs