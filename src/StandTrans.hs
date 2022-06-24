module StandTrans where
import Languages
import Data.List
import SahlqvistCheck

-- get all used variables in FOL formula
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

-- get vars in term 
varsInTerm :: Term -> [Int]
varsInTerm (VT (V n)) = [n]
varsInTerm (C _) = []

-- get vars as ints in var list
varsToInts :: [Var] -> [Int]
varsToInts [] = []
varsToInts [V n] = [n]
varsToInts ((V n):xs) = n : varsToInts xs


-- boxed atom primitive standard translation to FOL
standTransBxA :: ModFormBxA -> Var -> [Int] -> FOLFormVSAnt 
standTransBxA (NotBxA (NotBxA f)) x vars = standTransBxA f x vars
standTransBxA (PrpBxA k) x _ = Pc k (VT x)
standTransBxA (NotBxA (ConBxA (NotBxA f) (NotBxA g))) x vars = Disjc (standTransBxA f x vars : [standTransBxA g x 
    (vars ++ varsInFOLform2 (standTransBxA f x vars))])
standTransBxA (ConBxA f g) x vars = Conjc (standTransBxA f x vars : [standTransBxA g x 
    (vars ++ varsInFOLform2 (standTransBxA f x vars))])
standTransBxA (NotBxA (Nbox n (NotBxA f))) (V x) vars = diamondsR n vars x f
standTransBxA (Nbox n f) (V x) vars = (\y -> Forallc [V y] 
    (Impc (boxedR n vars x y) 
        (standTransBxA f (V y) (vars ++ getNthFresh n vars)))) (last (getNthFresh n vars))
standTransBxA TopBxA x _ = Eqdotc (VT x) (VT x)
standTransBxA (NotBxA f) x vars = Negc (standTransBxA f x vars)

-- ST of <>^n f 
diamondsR :: Int -> [Int] -> Int -> ModFormBxA -> FOLFormVSAnt
diamondsR 0 vars x f = standTransBxA f (V x) vars
diamondsR n vars x f = Existsc (map V (getNthFresh n vars))
    (Conjc 
        (zipWith (\ y1 y2 -> Rc (VT (V y1)) (VT (V y2)))
            (x : init (getNthFresh n vars)) (getNthFresh n vars) 
            ++ [standTransBxA f (V (last (getNthFresh n vars))) (vars ++ getNthFresh n vars)]
            ))

standTransBxAvX :: ModFormBxA -> FOLFormVSAnt 
standTransBxAvX f = standTransBxA f (V 0) [0]


-- special instance FOL corr.: uniform formulas
-- Pxi = xi =/= xi (P pos); Pxi = xi = xi (P neg)
standTransBxAUniform :: ModFormBxA -> ModFormBxA -> Var -> [Int] -> FOLFormVSAnt
standTransBxAUniform g (PrpBxA k) x _ | propPosNeg k g True = Negc (Eqdotc (VT x) (VT x))
                                    | propPosNeg k g False = Eqdotc (VT x) (VT x)
                                    | otherwise = undefined
standTransBxAUniform g (NotBxA (NotBxA f)) x vars = standTransBxAUniform g f x vars
standTransBxAUniform h (NotBxA (ConBxA (NotBxA f) (NotBxA g))) x vars = Disjc (standTransBxAUniform h f x vars : [standTransBxAUniform h g x 
    (vars ++ varsInFOLform2 (standTransBxAUniform h f x vars))])
standTransBxAUniform h (ConBxA f g) x vars = Conjc (standTransBxAUniform h f x vars : [standTransBxAUniform h g x 
    (vars ++ varsInFOLform2 (standTransBxAUniform h f x vars))])
standTransBxAUniform h (NotBxA (Nbox n (NotBxA f))) (V x) vars = diamondsRMonoUniform h n vars x f
standTransBxAUniform h (Nbox n f) (V x) vars = (\y -> Forallc [V y] 
    (Impc (boxedR n vars x y) 
        (standTransBxAUniform h f (V y) (vars ++ getNthFresh n vars)))) (last (getNthFresh n vars))
standTransBxAUniform _ TopBxA x _ = Eqdotc (VT x) (VT x)
standTransBxAUniform h (NotBxA f) x vars = Negc (standTransBxAUniform h f x vars)

diamondsRMonoUniform :: ModFormBxA -> Int -> [Int] -> Int -> ModFormBxA -> FOLFormVSAnt
diamondsRMonoUniform h 0 vars x f = standTransBxAUniform h f (V x) vars
diamondsRMonoUniform h n vars x f = Existsc (map V (getNthFresh n vars))
    (Conjc 
        (zipWith (\ y1 y2 -> Rc (VT (V y1)) (VT (V y2)))
            (x : init (getNthFresh n vars)) (getNthFresh n vars) 
            ++ [standTransBxAUniform h f (V (last (getNthFresh n vars))) (vars ++ getNthFresh n vars)]
            ))

-- get BxA substitutions right away, to use in minimal instances
standTransBxAgBA :: ModFormBxA -> Var -> [Int] -> [(Int, Int -> FOLFormVSAnt)] -> (FOLFormVSAnt, [(Int, Int -> FOLFormVSAnt)])
standTransBxAgBA (PrpBxA k) (V x) _ bxAs = (Pc k (VT (V x)), (k, Eqdotc (VT (V x)) . VT . V) : bxAs)
standTransBxAgBA (Nbox n (PrpBxA k)) (V x) vars bxAs = 
    (\y -> (Forallc [V y] 
    (Impc (boxedR n vars x y) 
        (Pc k (VT (V y)))), 
        bxAs ++ [(k, boxedR n vars x)]) ) (last (getNthFresh n vars))
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
