module Stand_trans where

import Languages

import Data.List
import Data.Maybe
import Data.Bifunctor

-- import SQ_shape

--- MODAL -> FOL 1

-- getFresh [] = 0
-- getFresh x = (maximum x) + 1

varsInFOLform :: FOLForm -> [Int]
varsInFOLform (P _ t) = varsInTerm t
varsInFOLform (R t1 t2) = nub (varsInTerm t1 ++ varsInTerm t2)
varsInFOLform (Eqdot t1 t2) = nub (varsInTerm t1 ++ varsInTerm t2)
varsInFOLform (Neg f) = varsInFOLform f
varsInFOLform (Conj f g) = nub (varsInFOLform f ++ varsInFOLform g)
varsInFOLform (Forall (V n) f) = nub (n : varsInFOLform f)
-- varsInFOLform (Exists (V n) f) = nub ([n] ++ varsInFOLform f)

varsInTerm :: Term -> [Int]
varsInTerm (VT (V n)) = [n]
varsInTerm (C _) = []

standTrans :: ModForm -> Var -> [Int] -> FOLForm
standTrans (Prp k) (V x) _ = P k (VT (V x))
standTrans Top (V x) _ = Eqdot (VT (V x)) (VT (V x))
standTrans (Con f g) (V x) li = Conj (standTrans f (V x) li) (standTrans g (V x) (li ++ varsInFOLform (standTrans f (V x) li)))
standTrans (Not (Not f)) (V x) li = standTrans f (V x) li
standTrans (Not f) (V x) li = Neg (standTrans f (V x) li)
standTrans (Box f) (V x) li = (\y -> Forall (V y) (impl (R (VT (V x)) (VT (V y))) (standTrans f (V y) (li ++ [y])))) (getFresh li)

trans_t :: [FOLForm]
trans_t = [(standTrans (Prp 0) (V 0) [0]),
            (standTrans (imp (Prp 0) (Prp 1)) (V 0) [0]),
    -- ((==) (standTrans (Box (Prp 0)) (V 0) [0]) (Forall (V 1) (impl (R (VT (V 0)) (VT (V 1))) (P 0 (VT (V 1))))))
    -- (standTrans (Con (Prp 0) (Not (Prp 1))) (V 0) [0]),
        -- (standTrans (Not (Con (Prp 0) (Not (Prp 1)))) (V 0) [0])
        (standTrans (dis (Box (Prp 0)) (dia (Prp 1)))) (V 0) [0]
--     -- (standTrans (Con (Prp 0) (Not (Prp 1))) (V 3)),
--     -- (standTrans (dia (Con (Prp 0) (Not (Prp 1)))) (V 0)),
    -- (standTrans bot (V 0) [0])
        ]

-- (==) (Forall (V 2) (P 0 (VT (V 2)))) (Forall (V 1) (P 0 (VT (V 1))))
-- (Forall (V 2) (P 0 (VT (V 2)))) '==' (Forall (V 1) (P 0 (VT (V 1))))


-- MODAl -> FOL2
varsInFOLform2 :: FOLFormVSAnt  -> [Int]
varsInFOLform2 (Pc _ t) = varsInTerm t
varsInFOLform2 (Rc t1 t2) = nub (varsInTerm t1 ++ varsInTerm t2)
varsInFOLform2 (Eqdotc t1 t2) = nub (varsInTerm t1 ++ varsInTerm t2)
varsInFOLform2 (Negc f) = varsInFOLform2 f
varsInFOLform2 (Conjc (x:xs)) = nub (varsInFOLform2 x ++ varsInFOLform2 (Conjc xs))
varsInFOLform2 (Disjc (x:xs)) = nub (varsInFOLform2 x ++ varsInFOLform2 (Disjc xs))
varsInFOLform2 (Impc f g) = nub (varsInFOLform2 f ++ varsInFOLform2 g)
varsInFOLform2 (Forallc vars f) = nub (varsToInts vars ++ varsInFOLform2 f)
varsInFOLform2 (Existsc vars f) = nub (varsToInts vars ++ varsInFOLform2 f)
varsInFOLform2 _ = []
-- varsInFOLform (Exists (V n) f) = nub ([n] ++ varsInFOLform f)

varsToInts :: [Var] -> [Int]
varsToInts [] = []
varsToInts [V n] = [n]
varsToInts ((V n):xs) = n : varsToInts xs

isBoxAt1 :: ModForm -> (Maybe Int, Maybe Int)
isBoxAt1 (Prp k) = (Just 0, Just k)
-- isBoxAt1 (Box f) = (plus (Just 1) (fst (isBoxAt1 f)), snd (isBoxAt1 f))
isBoxAt1 (Box f) = Data.Bifunctor.first (plus (Just 1)) (isBoxAt1 f)
isBoxAt1 _ = (Nothing, Nothing)


plus :: Maybe Int -> Maybe Int -> Maybe Int
plus (Just n) (Just m) = Just (m + n)
plus _ _ = Nothing

standTrans1 :: ModForm -> Var -> [Int] -> FOLFormVSAnt
standTrans1 f (V x) li | isJust(fst (isBoxAt1 f)) = 
    (\y -> Forallc [V y] (Impc 
        (boxedR (fromJust (fst (isBoxAt1 f))) li x y) 
        (Pc (fromJust (snd (isBoxAt1 f))) (VT (V y)))))  
    (last (getNthFresh (fromJust (fst (isBoxAt1 f))) li))
    | otherwise = standTrans2 f (V x) li-- =(\y -> Forallc [V y] (Impc (Rc (VT (V x)) (VT (V y))) (standTrans1 f (V y) (li ++ [y])))) (getFresh li)
-- standTrans1 (Prp k) (V x) _ = Pc k (VT (V x))

standTrans2 :: ModForm -> Var -> [Int] -> FOLFormVSAnt
standTrans2 Top (V x) _ = Eqdotc (VT (V x)) (VT (V x))
standTrans2 (Not (Not f)) (V x) li = standTrans1 f (V x) li
standTrans2 (Not (Con (Not f) (Not g))) x vars = Disjc (standTrans1 f x vars : [standTrans1 g x 
    (vars ++ varsInFOLform2 (standTrans1 f x vars))])
standTrans2 (Not (Con f (Not g))) x vars = Impc (standTrans1 f x vars) (standTrans1 g x 
    (vars ++ varsInFOLform2 (standTrans1 f x vars)))
standTrans2 (Con f g) (V x) li = Conjc (standTrans1 f (V x) li : [standTrans1 g (V x) (li ++ varsInFOLform (standTrans f (V x) li))])
standTrans2 (Not f) (V x) li = Negc (standTrans1 f (V x) li)
standTrans2 (Box f) (V x) li = (\y -> Forallc [V y] (Impc (Rc (VT (V x)) (VT (V y))) (standTrans2 f (V y) (li ++ [y])))) (getFresh li)
standTrans2 (Prp k) (V x) _ = Pc k (VT (V x))


sT1T :: [FOLFormVSAnt]
sT1T = [
    -- standTrans1 (Prp 0) (V 0) [0]

    -- standTrans1 (Box (Prp 0)) (V 0) [0]

    standTrans1 (imp (Box (Box (Prp 0))) (Prp 0))  (V 0) [0]
    -- standTrans1 (Box (Box (Not (Prp 0)))) (V 0) [0]

    ]

--- BOXAT

diamondsR :: Int -> [Int] -> Int -> ModFormBxA -> FOLFormVSAnt
-- diamondsR 0 vars x _ = (Eqdotc (VT (V x)) . VT . V) (getFresh vars)
diamondsR 0 vars x f = standTransBxA f (V x) vars
-- diamondsR n vars x f = Existsc (map V (getNthFresh n vars))
--     (Conjc 
--         (zipWith (\ y1 y2 -> Rc (VT (V y1)) (VT (V y2)))
--             (x : init (getNthFresh n vars)) (getNthFresh n vars) 
--             ++ [f (last (getNthFresh n vars))]
--             ))
diamondsR n vars x f = Existsc (map V (getNthFresh n vars))
    (Conjc 
        (zipWith (\ y1 y2 -> Rc (VT (V y1)) (VT (V y2)))
            (x : init (getNthFresh n vars)) (getNthFresh n vars) 
            ++ [standTransBxA f (V (last (getNthFresh n vars))) (vars ++ getNthFresh n vars)]
            ))

diamRT :: [FOLFormVSAnt]
diamRT = [
    diamondsR 0 [0] 0 (PrpBxA 1)
    ]

standTransBxA :: ModFormBxA -> Var -> [Int] -> FOLFormVSAnt 
-- standTransBxA (Nbox n k) (V x) vars = (\y -> Forallc [V y] (Impc 
--                     (boxedR n vars x y) (Pc k (VT (V y))))) 
--                         (last (getNthFresh n vars))
standTransBxA (NotBxA (NotBxA f)) x vars = standTransBxA f x vars
standTransBxA (PrpBxA k) x _ = Pc k (VT x)
-- standTransBxA (PrpBxA k) (V x) vars = (\y -> Forallc [V y] 
--     (Impc (boxedR 0 vars x y) 
--         (Pc k (VT (V y))))) (getFresh vars)
-- standTransBxA (NotBxA _) (V _) (_:_)
-- standTransBxAvX (NotBxA (ConBxA f ))
-- standTransBxA (NotBxA (NotBxA f)) x vars = standTransBxA f x vars

standTransBxA (NotBxA (ConBxA (NotBxA f) (NotBxA g))) x vars = Disjc (standTransBxA f x vars : [standTransBxA g x 
    (vars ++ varsInFOLform2 (standTransBxA f x vars))])
-- standTransBxA (NotBxA (ConBxA f (NotBxA g))) x vars = Impc 
--     (standTransBxA f x vars) (standTransBxA g x 
--     (vars ++ varsInFOLform2 (standTransBxA f x vars)))  
-- standTransBxA (NotBxA (ConBxA (NotBxA g) f)) x vars = Impc 
--     (standTransBxA f x vars) (standTransBxA g x 
--     (vars ++ varsInFOLform2 (standTransBxA f x vars)))
standTransBxA (ConBxA f g) x vars = Conjc (standTransBxA f x vars : [standTransBxA g x 
    (vars ++ varsInFOLform2 (standTransBxA f x vars))])

standTransBxA (NotBxA (Nbox n (NotBxA f))) (V x) vars = diamondsR n vars x f
standTransBxA (Nbox n f) (V x) vars = (\y -> Forallc [V y] 
    (Impc (boxedR n vars x y) 
        (standTransBxA f (V y) (vars ++ getNthFresh n vars)))) (last (getNthFresh n vars))
    -- (\y -> Existsc [V y] 
    --     (Conjc (Rc (VT x) (VT (V y)) : [standTransBxA f (V y) (vars ++ [y])])
    --     )) (getFresh vars)
standTransBxA TopBxA x _ = Eqdotc (VT x) (VT x)
standTransBxA (NotBxA f) x vars = Negc (standTransBxA f x vars)


-- get BxA substitutions right away
standTransBxAgBA :: ModFormBxA -> Var -> [Int] -> [(Int, Int -> FOLFormVSAnt)] -> (FOLFormVSAnt, [(Int, Int -> FOLFormVSAnt)])
standTransBxAgBA (PrpBxA k) (V x) vars bxAs = standTransBxAgBA (Nbox 0 (PrpBxA k)) (V x) vars bxAs
-- standTransBxA (PrpBxA k) (V x) vars bxAs = (\y -> (Forallc [V y] (Impc (Eqdotc (VT (V x)) (VT (V y)) (Pc k (VT (V y))))))) (getFresh vars)
-- standTransBxAgBA (PrpBxA k) (V x) vars bxAs = ((\y -> Forallc [V y] 
--     (Impc (Eqdotc (VT (V x)) (VT (V y))) (Pc k (VT (V y))))) (getFresh vars), 
--     (k, Eqdotc (VT (V x)) . VT . V) : bxAs) 
    -- standTransBxAgBA (NotBxA (Ndia 0 (NotBxA (PrpBxA k)))) (V x) vars bxAs
standTransBxAgBA (Nbox n (PrpBxA k)) (V x) vars bxAs = (\y -> (Forallc [V y] 
    (Impc (boxedR n vars x y) 
        (Pc k (VT (V y)))), 
        bxAs ++ [(k, boxedR n vars x)])) (last (getNthFresh n vars))
-- standTransBxAgBA f x vars bxAs = (standTransBxA f x vars, bxAs)
standTransBxAgBA (NotBxA (NotBxA f)) x vars bxAs = standTransBxAgBA f x vars bxAs
standTransBxAgBA (ConBxA f g) x vars bxAs = (Conjc 
    (fst (standTransBxAgBA f x vars bxAs) : [fst (standTransBxAgBA g x 
    (vars ++ varsInFOLform2 (fst (standTransBxAgBA f x vars bxAs))) bxAs)]), 
    snd (standTransBxAgBA f x vars bxAs) ++ snd (standTransBxAgBA g x 
    (vars ++ varsInFOLform2 (fst (standTransBxAgBA f x vars bxAs))) bxAs))
standTransBxAgBA TopBxA x _ bxAs = (Eqdotc (VT x) (VT x), bxAs)
standTransBxAgBA (NotBxA (Nbox n (NotBxA f))) (V x) vars bxAs = (diamondsR n vars x f, 
    snd (standTransBxAgBA f (V (last (getNthFresh n vars))) (vars ++ getNthFresh n vars) bxAs))
standTransBxAgBA _ _ _ _= undefined 
    -- standTransBxAgBA f x vars bxAs



-- standTransBxAgBA :: ModFormBxA -> Var -> [Int] -> [(Int, Int -> FOLFormVSAnt)] -> [FOLFormVSAnt] -> (FOLFormVSAnt, [(Int, Int -> FOLFormVSAnt)], [FOLFormVSAnt])
-- -- standTransBxA (PrpBxA k) (V x) vars bxAs = (\y -> (Forallc [V y] (Impc (Eqdotc (VT (V x)) (VT (V y)) (Pc k (VT (V y))))))) (getFresh vars)
-- standTransBxAgBA (PrpBxA k) (V x) vars bxAs bxAtrans = standTransBxAgBA (NotBxA (Ndia 0 (NotBxA (PrpBxA k)))) (V x) vars bxAs bxAtrans
-- standTransBxAgBA (NotBxA (Ndia n (NotBxA (PrpBxA k)))) (V x) vars bxAs bxAtrans = (\y -> (Forallc [V y] 
--     (Impc (boxedR n vars x y) 
--         (Pc k (VT (V y)))), 
--     bxAs ++ [(k, boxedR n vars x)],
--     bxAtrans ++ [Forallc [V y] 
--     (Impc (boxedR n vars x y) 
--         (Pc k (VT (V y))))]
--     )) (last (getNthFresh n vars))
-- standTransBxAgBA f x vars bxAs bxAtrs = (standTransBxA f x vars, bxAs, bxAtrs)

-- standTransBxA (ConBxA _ _) (V _) (_:_)
standTransBxAvX :: ModFormBxA -> FOLFormVSAnt 
standTransBxAvX f = standTransBxA f (V 0) [0]

stBxT :: [FOLFormVSAnt]
stBxT = [
    -- standTransBxAvX (impBxA (nBox 2 (PrpBxA 0)) (PrpBxA 0))

    -- standTransBxAvX (impBxA (Ndia 2 (ConBxA (PrpBxA 0) (Ndia 1 (nBox 1 (PrpBxA 1))))) (nBox 1 (disBxA (PrpBxA 0) (PrpBxA 1))))
    -- standTransBxAvX (impBxA TopBxA (PrpBxA 0))
    -- standTransBxAvX (NotBxA (Ndia 0 (NotBxA (PrpBxA 0))))
    -- standTransBxAvX (impBxA (Ndia 2 (PrpBxA 0)) (Ndia 1 (PrpBxA 0)))
    -- standTransBxAvX (impBxA (nBox 2 (PrpBxA 0)) (nBox 1 (PrpBxA 0)))
    -- standTransBxAvX (NotBxA (PrpBxA 0))
    -- standTransBxAvX (PrpBxA 0),
    -- standTransBxAvX (Nbox 0 0),
    -- standTransBxAvX (Nbox 1 0),
    -- standTransBxAvX (Nbox 2 0),
    -- standTransBxAvX (Nbox 3 0)
    ]

    -- (\(x,y,z) (a,b,c) -> (x+a, b*y, z-c)) (1,2,3) (4,5,6)