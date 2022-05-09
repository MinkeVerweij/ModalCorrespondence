module FOLCorrespondent where
import Languages
import SQ_shape
import Stand_trans

import Data.List



isSqAntBxA :: ModFormBxA -> Bool
isSqAntBxA TopBxA = True
isSqAntBxA (NotBxA TopBxA) = True
isSqAntBxA (PrpBxA _) = True 
isSqAntBxA (NotBxA (NotBxA f)) = isSqAntBxA f
-- isSqAntBxA (NotBxA (Box (Box f))) = isSqAntBxA (NotBxA f) -- ~[][] = <><>~
-- isSqAnt (Not (Box (Not f))) = isSqAntBxA f -- ~[]~ = <>
isSqAntBxA (Ndia _ f) = isSqAntBxA f
isSqAntBxA (ConBxA f g) = isSqAntBxA f && isSqAntBxA g
isSqAntBxA (NotBxA (Ndia _ (NotBxA (PrpBxA _)))) = True -- Boxed atoms
-- isSqAnt (Box f) = isBoxAt f
isSqAntBxA _ = False -- S

isNegativeBxA:: ModFormBxA -> Bool
isNegativeBxA TopBxA = True
isNegativeBxA (NotBxA TopBxA) = True
isNegativeBxA (PrpBxA _) = False
isNegativeBxA (NotBxA (PrpBxA _)) = True
isNegativeBxA (NotBxA (Ndia _ f)) = not (isNegativeBxA f)
isNegativeBxA (NotBxA (ConBxA f g)) = neither (isNegativeBxA f) (isNegativeBxA g)
isNegativeBxA (NotBxA (NotBxA f)) = isNegativeBxA f
isNegativeBxA (ConBxA f g) = isNegativeBxA f && isNegativeBxA g
isNegativeBxA (Ndia _ f) = isNegativeBxA f
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
vT = varsInFOLform2 (stTrAnt (impBxA (ConBxA (Ndia 2 (nBox 2 (PrpBxA 0))) (ConBxA (Ndia 1 (PrpBxA 1)) (nBox 1 (PrpBxA 2))))
         (Ndia 1 (disBxA (PrpBxA 0) (nBox 2 (PrpBxA 1))))))
    

tT :: [FOLFormVSAnt]
tT = [
        standTransBxA (getSqCsqBxA (impBxA (ConBxA (Ndia 2 (nBox 2 (PrpBxA 0))) (ConBxA (Ndia 1 (PrpBxA 1)) (nBox 1 (PrpBxA 2))))
         (Ndia 1 (disBxA (PrpBxA 0) (nBox 2 (PrpBxA 1)))))) (V 0) vT
    ]

pullDsT :: [FOLFormVSAnt]
pullDsT = [
    -- getPullDsFOL (impBxA (Ndia 2 (ConBxA (Ndia 1 (PrpBxA 1)) (nBox 2 (PrpBxA 0)))) (nBox 1 (PrpBxA 0)))
    getPullDsFOL (disBxA (NotBxA (Ndia 3 (PrpBxA 0))) (Ndia 1 (PrpBxA 0)))
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
    getSubstitution 0 (subsAnt (impBxA (ConBxA (nBox 2 (PrpBxA 0)) (PrpBxA 0)) (Ndia 1 (PrpBxA  0)))) 3
    ]

m :: [FOLFormVSAnt]
m = [bigDisj (minimalInst 0 [(0, boxedR 1 [0] 0), (1, boxedR 2 [0,1] 0), (0, boxedR 0 [0,1,2,3,4] 4)]) 8]
-- m = Disjc (map (minimalInst 0 [(0, boxedR 1 [0] 0)]))

-- getSubst :: [Int -> FOLFormVSAnt] -> (Int -> FOLFormVSAnt)
-- getSubst minInst = Disjc minInst

-- input :: Sq impl (S)
-- output :: FOL correspondent (unsimplified)
getFOLcorr :: ModFormBxA -> FOLFormVSAnt
getFOLcorr f = instantiate1 (getPullDsFOL f) (subsAnt f)

simSqT :: [FOLFormVSAnt]
simSqT = [
    -- getFOLcorr (impBxA (Ndia 2 (PrpBxA 0)) (Ndia 1 (PrpBxA 0)))
    getFOLcorr (impBxA (ConBxA (nBox 2 (PrpBxA 0)) (PrpBxA 0)) (Ndia 1 (PrpBxA  0)))
    -- getFOLcorr (impBxA (nBox 2 (PrpBxA 0)) (nBox 3 (PrpBxA 0)))
    -- getFOLcorr (impBxA (PrpBxA 0) (Ndia 1 (PrpBxA 0)))
    -- getFOLcorr (impBxA (Ndia 1 (PrpBxA 0)) (Ndia 2 (PrpBxA 0)))
    -- getFOLcorr (impBxA (ConBxA (PrpBxA 0) (Ndia 2 (PrpBxA 0))) (Ndia 1 (PrpBxA 0)))
    -- getFOLcorr (impBxA (PrpBxA 0) (PrpBxA 1))
    -- getFOLcorr (impBxA TopBxA (Ndia 1 (nBox 1 (PrpBxA 0))))
    -- getFOLcorr (disBxA (NotBxA (Ndia 3 (PrpBxA 0))) (Ndia 2 (PrpBxA 0)))
    -- getFOLcorr (impBxA (ConBxA (Ndia 2 (nBox 2 (PrpBxA 0))) (ConBxA (Ndia 1 (PrpBxA 1)) (nBox 1 (PrpBxA 2))))
    --      (Ndia 1 (disBxA (PrpBxA 0) (nBox 2 (PrpBxA 1)))))
    -- getFOLcorr (disBxA (disBxA (NotBxA (PrpBxA 0)) (NotBxA (Ndia 2 (PrpBxA 0)))) (Ndia 1 (PrpBxA 0)))
    ]