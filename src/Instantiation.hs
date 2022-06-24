module Instantiation where
import Languages
import StandTrans
import Data.List
import SahlqvistCheck

{-
    First formulas concerning the 'pull diamonds' step,
    then 'reading of instances and instantiating'.
-}
-- get FO formula after pulling diamonds
getPullDsFOL :: ModFormBxA -> FOLFormVSAnt
getPullDsFOL f = Forallc (fst (pullDiamonds1 (standTransAnt f))) 
    (Impc 
        (Conjc (snd (pullDiamonds1 (standTransAnt f)))) 
        (standTransBxA (getSqCsqBxA f) (V 0) (varsInFOLform2 (standTransAnt f)))
    )


-- input: Sq Antecedent (S)
-- output: diavars, REL, (Sub BoxAtom: k (P id), sigma(P_k))
pullDiamonds1 :: FOLFormVSAnt -> ([Var], [FOLFormVSAnt])
pullDiamonds1 f = getDiaRels f [] []

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

-- standard translation of antecedent (at x)
standTransAnt :: ModFormBxA -> FOLFormVSAnt
standTransAnt f = fst (standTransBxAgBA (getSqAntBxA f) (V 0) [0] [])

-- substitution 'dictionary' of antecedent
-- get (Pred id int, substitution as function of variable id int)
getSubstitutionsFromAnt :: ModFormBxA  -> [(Int, Int -> FOLFormVSAnt)]
getSubstitutionsFromAnt f = snd (standTransBxAgBA (getSqAntBxA f) (V 0) [0] [])

-- get minimal instances for every predicate
-- input: Pred. id, list of all possible substitutions [(pred id, subst(var))]
-- output: list of substitutions for given pred id
minimalInst :: Int -> [(Int, Int -> FOLFormVSAnt)] -> [Int -> FOLFormVSAnt]
minimalInst k subs = map snd $ filter ((==k) . fst) subs

-- makes disjunction over minimal instances provided a predicate (id)
-- output: disj. of all subst. of given predicate, s.t. 1 var can be applied
getSubstitution :: Int -> [(Int, Int -> FOLFormVSAnt)] -> (Int -> FOLFormVSAnt)
getSubstitution k subs y = Disjc [ f y | f <- minimalInst k subs ]

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

{- Helper functions to get Sq antecedent and consequent respectively -}
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