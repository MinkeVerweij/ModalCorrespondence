module VsimpleSq where

import Languages
import Stand_trans
import SQ_shape
-- import Data.List

getSqAnt :: ModForm -> ModForm -- has to been through Sq check (+ be imp)
getSqAnt (Not (Not f)) = getSqAnt f
getSqAnt (Not (Con f g)) | isSqAnt f && isNegative g = f -- f -> ~g
                        | isSqAnt g && isNegative f = g -- g -> ~f
                        | otherwise = undefined
getSqAnt _ = undefined

getSqCsq :: ModForm -> ModForm -- has to been through Sq check (+ be imp)
getSqCsq (Not (Not f)) = getSqCsq f
getSqCsq (Not (Con f g)) | isSqAnt f && isNegative g = Not g -- f -> ~g
                        | isSqAnt g && isNegative f = Not f -- g -> ~f
                        | otherwise = undefined
getSqCsq _ = undefined


modSimp1 :: ModForm -> ModForm -- eliminate double neg: ~~f = f 
modSimp1 (Prp k) = Prp k
modSimp1 Top = Top
modSimp1 (Not (Not f)) = f
modSimp1 (Not (Box (Not (Not f)))) = Not (Box (modSimp1 f)) -- <>~

modSimp1 (Not (Con (Not (Not f)) (Not (Not g)))) = Not (Con (modSimp1 f) (modSimp1 g))
modSimp1 (Not (Con (Not (Not f)) g)) = Not (Con (modSimp1 f) (modSimp1 g))
modSimp1 (Not (Con f (Not (Not g)))) = Not (Con (modSimp1 f) (modSimp1 g))

modSimp1 (Not f) = Not (modSimp1 f)
modSimp1 (Con f g) = Con (modSimp1 f) (modSimp1 g)
modSimp1 (Box f) = Box (modSimp1 f)


-- data FOLFormVSAnt = Pc Int Term | Rc Term Term | Eqdotc Term Term |
--                     Negc FOLFormVSAnt | 
--                     Conjc [FOLFormVSAnt] |
--                     Impc FOLFormVSAnt FOLFormVSAnt | 
--                     Disjc [FOLFormVSAnt] |
--                     Forallc [Var] FOLFormVSAnt
--                     deriving(Eq, Ord, Show)

-- standTrans1 :: ModForm -> Var -> [Int] -> FOLFormVSAnt
-- standTrans1 (Prp k) (V x) _ = (Pc k (VT (V x)))
-- standTrans1 Top (V x) _ = (Eqdotc (VT (V x)) (VT (V x)))
-- standTrans1 (Con f g) (V x) li = (Conjc ([standTrans1 f (V x) li] ++ [standTrans1 g (V x) (li ++ (varsInFOLform (standTrans f (V x) li)))]))
-- standTrans1 (Not (Not f)) (V x) li = (standTrans1 f (V x) li)
-- standTrans1 (Not f) (V x) li = (Negc (standTrans1 f (V x) li))
-- standTrans1 (Box f) (V x) li = (\y -> Forallc [(V y)] (Impc (Rc (VT (V x)) (VT (V y))) (standTrans1 f (V y) (li ++ [y])))) (getFresh li)

getAtoms :: FOLForm -> [FOLFormVSAnt] -- get list of Predicates in FOLForm
getAtoms (P k t) = [Pc k t]
getAtoms (Eqdot _ _) = []
getAtoms (R _ _) = []
getAtoms (Conj f g) = getAtoms f ++ getAtoms g
getAtoms (Neg f) = getAtoms f
getAtoms (Forall (V _) f) = getAtoms f

boxCounterPrp :: ModForm -> Int -> (Int, Int)
boxCounterPrp (Box f) k = boxCounterPrp f (k+1)
boxCounterPrp (Prp j) k = (k, j)
boxCounterPrp _ _ = undefined 

getBoxedAtoms :: ModForm  -> Int -> [Int] -> [(FOLFormVSAnt, Int -> FOLFormVSAnt)]
getBoxedAtoms (Prp k) x vars = [(Pc k (VT (V x)), boxedR 0 vars x)]
getBoxedAtoms (Con f g) x vars = getBoxedAtoms f x vars ++ getBoxedAtoms g x vars
getBoxedAtoms (Box f) x vars | isBoxAt (Box f) = [(Pc (snd (boxCounterPrp f 1)) (VT (V (last (x : getNthFresh x vars)))), 
                                                boxedR (fst (boxCounterPrp f 1)) vars x)]
getBoxedAtoms _ _ _ = []

getBoxAtT :: [FOLFormVSAnt] -- [[(FOLFormVSAnt, Int -> FOLFormVSAnt)]]
getBoxAtT = [
    -- getBoxedAtoms (Prp 0) 0 [0],
    snd (head (getBoxedAtoms (Box (Prp 1)) 0 [0])) 99,
    snd (head (getBoxedAtoms (Box (Box (Prp 1))) 0 [0])) 99
    ]

getRels :: FOLForm -> [FOLFormVSAnt] -- get list of Predicates in FOLForm
getRels (P _ _) = []
getRels (Eqdot _ _) = []
getRels (R t1 t2) = [Rc t1 t2]
getRels (Conj f g) = getRels f ++ getRels g
getRels (Neg f) = getRels f
getRels (Forall (V _) f) = getRels f

getDiamonds :: FOLForm -> [Var]
-- getDiamonds Top = []
getDiamonds (Eqdot _ _) = []
getDiamonds (P _ _) = []
getDiamonds (R _ _) = []
getDiamonds (Neg (Forall (V k) f)) = V k : getDiamonds f
getDiamonds (Neg f) = getDiamonds f
getDiamonds (Conj f g) = getDiamonds f ++ getDiamonds g
getDiamonds (Forall _ f) = getDiamonds f


-- currying standtrans
standTransAtx :: ModForm -> FOLForm
standTransAtx f = standTrans f (V 0) [0]

standTransAtx1 :: ModForm -> FOLFormVSAnt 
standTransAtx1 f = standTrans1 f (V 0) [0]

standTransCsq :: ModForm -> FOLFormVSAnt
standTransCsq f = standTrans1 (getSqCsq f) (V 0) (varsInFOLform (standTransAtx (getSqAnt f)))


boxAtST :: [FOLFormVSAnt]
boxAtST = [
    -- standTransAtx1 (modSimp1 (getSqAnt (imp (Box (Prp 0)) (Box (Box (Prp 0))))))
    standTransAtx1 (modSimp1 (getSqAnt (imp (Box (Box (Prp 0))) (Box (Box (Prp 0))))))
    
    ]

boxCounter :: ModForm -> Int -> Int
boxCounter (Box f) k = boxCounter f (k+1)
boxCounter _ k = k



-- input: n: #Boxes k: PredID x: varID (0) [Int] : used var IDS
-- output: Ex y1 (Rxy1 & (Ex y2(Ry1y2 & ... & Ex y(n-1)(Ry(n-2)y(n-1) & Ry(n-1)yn)))))
-- standTransRBoxAt :: Int -> Int -> Int -> [Int] -> FOLFormVSAnt
-- standTransRBoxAt 0 k x vars = (\y -> Eqdotc (VT (V x)) (VT (V y))) (getFresh vars)
-- standTransRBoxAt 1 k x vars = (\y -> Rc (VT (V x)) (VT (V y))) (getFresh vars)
-- standTransRBoxAt n k x vars = 
-- standTransBoxAt :: Int -> Int -> Int -> FOLFormVSAnt
-- standTransBoxAt 0 k x = (\y -> Forallc [V y] (Impc (Eqdotc (VT (V x)) (VT (V y))) (Pc k (VT (V x))))) (last (getNthFresh 1 [x]))
-- standTransBoxAt n k x = (\y -> Forallc [V y] (Impc ))


-- pullDiamonds2 :: ModForm -> Int -> [Int] -> FOLFormVSAnt 
-- pullDiamonds2 f | getDiamonds (standTransAtx (modSimp1 (getSqAnt f))) /= [] =
--     (Forallc (getDiamonds (standTransAtx (modSimp1 (getSqAnt f)))) 
--         (Impc
--             (Conjc ()
--             )
--             (standTransCsq f)
--         )
--     )




-- input: VS Sq ModForm 
-- output: (Forall ... (REL & AT -> POS), [AT])
pullDiamonds :: ModForm -> (FOLFormVSAnt, [FOLFormVSAnt])
pullDiamonds f | getDiamonds (standTransAtx (modSimp1 (getSqAnt f))) /= [] =
    (Forallc (getDiamonds (standTransAtx (modSimp1 (getSqAnt f)))) 
        (Impc
            (Conjc 
                (getAtoms (standTransAtx (modSimp1 (getSqAnt f))) ++ getRels (standTransAtx (modSimp1 (getSqAnt f))))) 
            (standTransCsq f)), 
    getAtoms (standTransAtx (modSimp1 (getSqAnt f))))
        | otherwise = (Impc 
            (Conjc (getAtoms (standTransAtx (modSimp1 (getSqAnt f))))) 
            (standTransCsq f), 
        getAtoms (standTransAtx (modSimp1 (getSqAnt f))))


pd_t :: [(FOLFormVSAnt, [FOLFormVSAnt])]
pd_t = [
    -- (pullDiamonds (imp (Prp 0) (dia (Prp 0))))
        -- (pullDiamonds (imp (dia (Prp 0)) (dia (dia (Prp 0)))))
        -- (pullDiamonds (imp (dia (dia (Prp 0))) (dia (Prp 0))))
        -- (pullDiamonds (imp (Con (Prp 0) (dia (Prp 1))) (Box (dia (Prp 1)))))
        -- (pullDiamonds (imp (dia (dia (Con (Prp 0) (dia (Prp 0))))) (Box (Prp 0))))
        ]


-- input: terms of AT [v_1,..., v_n] (vars at which certain antecedent predicate holds)
-- output lambda u.(u=v_1 || u=v_2 || .. || u=v_n)
substitutionAT :: [Term] -> (Term -> FOLFormVSAnt)
substitutionAT [t] = \y -> (Eqdotc y t)
substitutionAT ts = \y -> Disjc (map (\t -> (Eqdotc y t)) ts)
-- readInstances k ts = map (\y -> (map (\t -> Disjc (y Eqdotc t)) ts))

sub_t :: [FOLFormVSAnt]
sub_t = [
        (substitutionAT [(VT (V 0)), (VT (V 1))]) (VT (V 3))
    ]

-- input: Pred. identifying int k, AT [P k (VT (V i))] (P_k x_i's of antecedent)
-- output: [(VT (V j))] s.t P_k x_j in AT
minimalInstances :: Int -> [FOLFormVSAnt] -> [Term]
-- minimalInstances k [] = []
minimalInstances k ((Pc j t):xs) | k == j = t : minimalInstances k xs
minimalInstances _ _ = []

getAT :: ModForm -> [FOLFormVSAnt]
getAT f = snd (pullDiamonds f)

min_t :: [[Term]]
min_t = [
            (minimalInstances 0 (getAT (imp (Prp 0) (dia (Prp 0))))),
            (minimalInstances 1 (getAT (imp (Prp 1) (dia (Prp 0))))),
            (minimalInstances 0 (getAT (imp (Prp 0) (Prp 0))))
        ]

-- inputs: Forall ... (REL & AT -> POS), [AT] (pullDiamonds output)
-- output: FOL formula
instantiate :: FOLFormVSAnt -> [FOLFormVSAnt] -> FOLFormVSAnt
instantiate (Pc k t) at | minimalInstances k at /= [] =
                        substitutionAT (minimalInstances k at) t
                        | otherwise = Negc (Eqdotc t t) -- P_k only in Csq (positive)
instantiate (Rc t1 t2) _ = Rc t1 t2
instantiate (Negc f) at = Negc (instantiate f at)
instantiate (Conjc cs) at = Conjc (map (`instantiate` at) cs)
instantiate (Disjc cs) at = Disjc (map (`instantiate` at) cs)
-- instantiate (Conjc cs) at = Conjc (map (\c -> (instantiate c at)) cs)
-- instantiate (Disjc cs) at = Disjc (map (\c -> (instantiate c at)) cs)
instantiate (Impc f g) at = Impc (instantiate f at) (instantiate g at)
instantiate (Forallc vars f) at = Forallc vars (instantiate f at)
instantiate (Eqdotc t1 t2) _ = Eqdotc t1 t2
instantiate (Existsc vars f) at = Existsc vars (instantiate f at)
instantiate Topc _ = Topc

-- (substitutionAT (minimalInstances 0 (getAT (imp (Prp 0) (Prp 0)))) (VT (V 0)))

getFOL :: ModForm -> FOLFormVSAnt --input VS Sq
-- getFOL f = instantiate (fst (pullDiamonds f)) (snd (pullDiamonds f))
getFOL f = uncurry instantiate (pullDiamonds f)

vs_test :: [FOLFormVSAnt]
vs_test = [
    -- (instantiate (fst (pullDiamonds (imp (Prp 0) (dia (Prp 0))))) (snd (pullDiamonds (imp (Prp 0) (dia (Prp 0))))))
    -- getFOL (imp (Prp 0) (dia (Prp 0)))
    -- getFOL (imp (dia (Prp 0)) (dia (dia (Prp 0))))
    -- getFOL (imp (Con (Prp 0) (dia (dia (Prp 0)))) (dia (Prp 0)))
    -- getFOL (imp (Prp 0) (Prp 1))
    -- getFOL (imp Top (dia (Box (Prp 0))))
    getFOL (dis (Not (dia (dia (Prp 0)))) (dia (Prp 0)))
    ]