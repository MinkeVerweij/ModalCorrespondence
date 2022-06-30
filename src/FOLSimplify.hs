module FOLSimplify where

import Languages
import Data.List
import Data.Maybe
import Data.Bifunctor
{- Simplification of FOL formulas -}

-- general simplify first, then simplify 'Exists v_i (x=v_i & a(v_i))' to a(x)
simpFOL3 :: FOLForm -> FOLForm
simpFOL3 f = simpFOL2 (simpFOL1 f)

-- general simplification
simpFOL :: FOLForm -> FOLForm
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
simpFOL (Impc f (Disjc gs)) | f `elem` gs = Topc
simpFOL (Impc f (Existsc _ (Disjc gs))) | f `elem` gs = Topc
simpFOL (Impc (Conjc fs) (Disjc gs)) | not (null (fs `intersect` gs)) = Topc
simpFOL (Impc f g) | f == g = Topc
                | otherwise = Impc (simpFOL f) (simpFOL g)
simpFOL (Forallc vars (Impc f (Forallc vars2 (Impc g h)))) =  
    Forallc (vars ++ vars2) (simpFOL (Impc (Conjc (flattenCon [f, g])) h))
simpFOL (Forallc [] f) = simpFOL f
simpFOL (Forallc xs f) = remUnusedQuantVar (Forallc xs (simpFOL f))

simpFOL (Existsc [] f) = simpFOL f
simpFOL (Existsc xs f) = remUnusedQuantVar (Existsc xs (simpFOL f))

simpFOL f = f

-- continue general until no changes
simpFOL1 :: FOLForm -> FOLForm
simpFOL1 f | simpFOL f == f = f 
            | otherwise = simpFOL1 (simpFOL f)

flattenCon :: [FOLForm] -> [FOLForm]
flattenCon [] = []
flattenCon (Conjc fs:gs) = fs ++ flattenCon gs
flattenCon (f:fs) = f : flattenCon fs

flattenDis :: [FOLForm] -> [FOLForm]
flattenDis [] = []
flattenDis (Disjc fs:gs) = fs ++ flattenDis gs
flattenDis (f:fs) = f : flattenDis fs

-- instantiate possible existentials and simplify again
simpFOL2 :: FOLForm -> FOLForm
simpFOL2 f | simpExAND f == f = f
        | otherwise = simpFOL1 (simpExAND f)

{- instantiate possible existentials
    'Exists v_i (x=v_i & a(v_i))' => a(x)
        can also be ORs within AND, need to keep OR
-}
simpExAND :: FOLForm -> FOLForm
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
disjOuter :: FOLForm -> [FOLForm] -> FOLForm
disjOuter (Conjc (Disjc gs:_)) hs = Disjc (map (\g -> Conjc (g: (hs \\ [Disjc gs]))) gs)
disjOuter (Conjc (_:fs)) hs = disjOuter (Conjc fs) hs
disjOuter (Conjc []) hs = Conjc hs
disjOuter _ _= undefined

getDCjuncts :: FOLForm -> [FOLForm]
getDCjuncts (Disjc fs) = fs
getDCjuncts (Conjc fs) = fs
getDCjuncts _ = undefined

-- Only quantify over variables that are in formula f (Qx f) 
remUnusedQuantVar :: FOLForm -> FOLForm
remUnusedQuantVar (Existsc vars f) = Existsc (filter (`varInForm` f) vars) f
remUnusedQuantVar (Forallc vars f) = Forallc (filter (`varInForm` f) vars) f
remUnusedQuantVar f = f

-- Exists (Conj fs) w/ fs has no disjuncts
exANDVarEq :: [Var] -> [FOLForm] -> FOLForm
exANDVarEq (V x:xs) fs | isJust (getEqVar x fs) = 
         simpFOL1 (Conjc [varsSub [x] [fromJust (getEqVar x fs)] f | f <- fs])
            | otherwise = exANDVarEq xs fs

exANDVarEq [] fs = simpExAND (simpFOL1 (Conjc fs))

-- Exists (Disj fs) w/ fs conjunctions
exORANDSVarEq1 :: [Var] -> [[FOLForm]] -> FOLForm
exORANDSVarEq1 vars fss = Disjc (exORANDSVarEq vars fss)

exORANDSVarEq :: [Var] -> [[FOLForm]] -> [FOLForm]
exORANDSVarEq vars = map (exANDVarEq vars)

-- get the variable that the quantified var is equal to, if any
getEqVar :: Int -> [FOLForm] -> Maybe Int
getEqVar x ((Eqdotc (VT (V i)) (VT (V j))):fs) 
                                    | i == x = Just j
                                    | j == x = Just i
                                    | otherwise = getEqVar x fs
getEqVar x (_:fs) = getEqVar x fs
getEqVar _ [] = Nothing

{- simplifying/expanding for visualization-}

simpFOLViz2 :: FOLForm -> FOLForm
simpFOLViz2 f = simpFOLViz1 (simpFOLpushNeg1 f)

simpFOLpushNeg :: FOLForm -> FOLForm
simpFOLpushNeg (Negc (Conjc fs)) =  Disjc [simpFOL2 (simpFOLpushNeg (simpFOL1 (Negc f)))|f<- fs]
simpFOLpushNeg (Negc (Impc f g)) = Conjc [simpFOL1 f, simpFOL1 (Negc g)]
simpFOLpushNeg (Negc (Existsc vars f)) = Forallc vars (simpFOLpushNeg (simpFOL1 (Negc f)))
simpFOLpushNeg (Negc (Forallc vars f)) = Existsc vars (simpFOLpushNeg (simpFOL1 (Negc f)))
simpFOLpushNeg (Conjc fs) = Conjc [simpFOLpushNeg f | f<- fs]
simpFOLpushNeg (Disjc fs) = Disjc [simpFOLpushNeg f | f<- fs]
simpFOLpushNeg (Existsc vars f) = Existsc vars (simpFOLpushNeg f)
simpFOLpushNeg (Forallc vars f) = Forallc vars (simpFOLpushNeg f)
simpFOLpushNeg (Impc f g) = Impc (simpFOLpushNeg f) (simpFOLpushNeg g)
simpFOLpushNeg f = simpFOL1 f


simpFOLpushNeg1 :: FOLForm -> FOLForm
simpFOLpushNeg1 f | simpFOLpushNeg f == f = f
        | otherwise = simpFOLpushNeg1 (simpFOLpushNeg f)

simpFOLViz1 :: FOLForm -> FOLForm
simpFOLViz1 f | simpFOLViz f == f = f
            | otherwise = simpFOL1 (simpFOLViz1 (simpFOLViz f))

-- splitting implied conjuncts/disjuncts, transforming disjunctions into implications (if possible)
simpFOLViz :: FOLForm -> FOLForm
simpFOLViz (Forallc vars (Impc f (Forallc vars2 (Impc g h)))) = 
    simpFOLViz (Forallc (vars ++ vars2)  (simpFOL1 (Impc (Conjc (flattenCon [f, g])) h)))
simpFOLViz (Forallc vars (Impc f (Existsc vars2 (Conjc gs)))) | hasForAllImp gs = -- expand conj.
       Forallc vars (Existsc vars2 (Conjc [simpFOLViz (Impc f g) | g <- gs])) 
simpFOLViz (Forallc vars (Impc f (Conjc gs))) = Conjc [simpFOLViz (Forallc vars (Impc f g)) | g <- gs]
simpFOLViz (Forallc vars (Impc f (Disjc gs))) --  expand disj
    | hasForAllImp gs = Forallc vars (Disjc [simpFOLViz (Impc f g) | g <- gs])
simpFOLViz (Conjc fs) -- flatten conj. (also pull back quantifiers)
    | not (null (snd1 (getVarsForallExForms fs))) = 
        Forallc (snd1 (getVarsForallExForms fs)) (Existsc (thrd (getVarsForallExForms fs)) (Conjc (fst1 (getVarsForallExForms fs))))
    | not (null (snd (getVarsExForms fs))) = Existsc (snd (getVarsExForms fs)) (simpFOLViz (Conjc (flattenCon (fst (getVarsExForms fs)))))
    | otherwise =    Conjc (flattenCon [simpFOLViz f | f <- fs])
simpFOLViz (Disjc fs) -- disj -> imp? or flatten disj.
    | not (null (negForms fs)) && not (null (posForms fs)) = simpFOLViz (simpFOL3 (Impc (Conjc (negForms fs)) (Disjc (posForms fs))))
    | not (null (negForms fs)) && length fs > 1 = simpFOLViz (simpFOL3 (Impc (Conjc (init (negForms fs))) (Negc (last (negForms fs)))))
    | otherwise = Disjc (flattenDis [simpFOLViz f | f <- fs])
simpFOLViz (Existsc vars (Conjc fs)) -- flatten conj.
    | not (null (snd (getVarsExForms fs))) = Existsc (vars ++ snd (getVarsExForms fs)) (simpFOLViz (Conjc (flattenCon (fst (getVarsExForms fs)))))
    | otherwise = Existsc vars (Conjc (flattenCon [simpFOLViz f | f <- fs]))
simpFOLViz (Existsc vars (Disjc fs)) = Existsc vars (Disjc (flattenDis [simpFOLViz f | f <- fs])) -- flatten disj.
simpFOLViz (Existsc vars f) = Existsc vars (simpFOLViz f)
simpFOLViz (Forallc vars f) = Forallc vars (simpFOLViz f)
simpFOLViz (Impc f (Forallc vars (Impc g h))) = simpFOLViz (Forallc vars (simpFOL1 (Impc (Conjc (flattenCon [f, g])) h)))
simpFOLViz (Impc f (Forallc vars g)) = simpFOLViz (Forallc vars (Impc f g))
simpFOLViz (Impc f (Existsc vars2 (Conjc gs))) | hasForAllImp gs = Existsc vars2 (Conjc [simpFOLViz (Impc f g) | g <- gs])
simpFOLViz (Impc f (Conjc gs)) = Conjc [simpFOLViz (Impc f g)| g <- gs]
simpFOLViz (Impc f (Disjc gs)) | hasForAllImp gs = Disjc [simpFOLViz (Impc f g) | g <- gs]
simpFOLViz (Impc f g) = Impc (simpFOLViz f) (simpFOLViz g)
simpFOLViz (Negc f) = Negc (simpFOLViz f)
simpFOLViz f = f

-- check complexity of implied conjucntion/disjucntion (complex -> visualize w/ extra cluster)
hasForAllImp :: [FOLForm] -> Bool
hasForAllImp [] = False
hasForAllImp ((Impc _ _) :_) = True
hasForAllImp ((Forallc _ (Impc _ _)):_) = True
hasForAllImp ((Forallc _ (Existsc _ _)):_) = True
hasForAllImp ((Existsc _ (Conjc fs)):rest) = hasForAllImp fs || hasForAllImp rest
hasForAllImp ((Existsc _ (Disjc fs)):rest) = hasForAllImp fs || hasForAllImp rest
hasForAllImp ((Disjc fs):rest) = hasForAllImp fs || hasForAllImp rest
hasForAllImp ((Conjc fs):rest) = hasForAllImp fs || hasForAllImp rest
hasForAllImp (_:fs) = hasForAllImp fs

-- get existential formulas (from conjuncts)
getVarsExForms :: [FOLForm] -> ([FOLForm], [Var])
getVarsExForms [] = ([],[])
getVarsExForms ((Existsc vars f):fs) | hasForAllImp [f] = bimap (f :) (vars ++) (getVarsExForms fs)
getVarsExForms (f:fs) = bimap (f :) ([] ++) (getVarsExForms fs)

trimap :: ([FOLForm] -> [FOLForm]) -> ([Var] -> [Var]) -> ([Var] -> [Var])  -> ([FOLForm], [Var], [Var]) -> ([FOLForm], [Var], [Var])
trimap f1 f2 f3 (fs, vs1, vs2) = (f1 fs, f2 vs1, f3 vs2)

fst1 :: ([FOLForm], [Var], [Var]) -> [FOLForm]
fst1 (fs,_,_) = fs

snd1 ::  ([FOLForm], [Var], [Var]) -> [Var]
snd1 (_,vs,_) = vs

thrd ::  ([FOLForm], [Var], [Var]) -> [Var]
thrd (_, _,vs) = vs

-- get universally quantified existential formulas (from conjuncts)
getVarsForallExForms :: [FOLForm] -> ([FOLForm], [Var], [Var]) -- fs univVars existVars
getVarsForallExForms [] = ([],[],[])
getVarsForallExForms ((Forallc vars (Existsc vars2 f)):fs) = trimap (f :) (vars ++) (vars2 ++) (getVarsForallExForms fs)
getVarsForallExForms (f:fs) = trimap (f :) ([] ++) ([] ++) (getVarsForallExForms fs)

{- 
    Helper functions to work with variables
-}
-- check whether a variable is in a formula
varInForm :: Var -> FOLForm -> Bool
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
varsSub :: [Int] -> [Int] -> FOLForm -> FOLForm
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

posForms :: [FOLForm] -> [FOLForm]
posForms [] = []
posForms ((Negc _):fs) = posForms fs
posForms (f:fs) = f : posForms fs

negForms :: [FOLForm] -> [FOLForm]
negForms [] = []
negForms ((Negc f):fs) = f : negForms fs
negForms (_:fs) = negForms fs