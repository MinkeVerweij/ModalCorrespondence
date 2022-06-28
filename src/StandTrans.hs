module StandTrans where
import Languages
import Data.List
import SahlqvistCheck

-- get all used variables in FOL formula
varsInFOLform :: FOLForm  -> [Int]
varsInFOLform (Pc _ t) = varsInTerm t
varsInFOLform (Rc t1 t2) = nub (varsInTerm t1 ++ varsInTerm t2)
varsInFOLform (Eqdotc t1 t2) = nub (varsInTerm t1 ++ varsInTerm t2)
varsInFOLform (Negc f) = varsInFOLform f
varsInFOLform (Conjc (x:xs)) = nub (varsInFOLform x ++ varsInFOLform (Conjc xs))
varsInFOLform (Disjc (x:xs)) = nub (varsInFOLform x ++ varsInFOLform (Disjc xs))
varsInFOLform (Impc f g) = nub (varsInFOLform f ++ varsInFOLform g)
varsInFOLform (Forallc vars f) = nub (varsToInts vars ++ varsInFOLform f)
varsInFOLform (Existsc vars f) = nub (varsToInts vars ++ varsInFOLform f)
varsInFOLform _ = []

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
standTransBxA :: ModFormBxA -> Var -> [Int] -> FOLForm 
standTransBxA (NotBxA (NotBxA f)) x vars = standTransBxA f x vars
standTransBxA (PrpBxA k) x _ = Pc k (VT x)
standTransBxA (NotBxA (ConBxA (NotBxA f) (NotBxA g))) x vars = Disjc (standTransBxA f x vars : [standTransBxA g x 
    (vars ++ varsInFOLform (standTransBxA f x vars))])
standTransBxA (ConBxA f g) x vars = Conjc (standTransBxA f x vars : [standTransBxA g x 
    (vars ++ varsInFOLform (standTransBxA f x vars))])
standTransBxA (NotBxA (Nbox n (NotBxA f))) (V x) vars = diamondsR n vars x f
standTransBxA (Nbox n f) (V x) vars = (\y -> Forallc [V y] 
    (Impc (boxedR n vars x y) 
        (standTransBxA f (V y) (vars ++ getNthFresh n vars)))) (last (getNthFresh n vars))
standTransBxA TopBxA x _ = Eqdotc (VT x) (VT x)
standTransBxA (NotBxA f) x vars = Negc (standTransBxA f x vars)

-- ST of <>^n f 
diamondsR :: Int -> [Int] -> Int -> ModFormBxA -> FOLForm
diamondsR 0 vars x f = standTransBxA f (V x) vars
diamondsR n vars x f = Existsc (map V (getNthFresh n vars))
    (Conjc 
        (zipWith (\ y1 y2 -> Rc (VT (V y1)) (VT (V y2)))
            (x : init (getNthFresh n vars)) (getNthFresh n vars) 
            ++ [standTransBxA f (V (last (getNthFresh n vars))) (vars ++ getNthFresh n vars)]
            ))

-- standTransBxAvX :: ModFormBxA -> FOLForm 
-- standTransBxAvX f = standTransBxA f (V 0) [0]


-- special instance FOL corr.: uniform formulas
-- Pxi = xi =/= xi (P pos); Pxi = xi = xi (P neg)
stUniform :: ModFormBxA -> ModFormBxA -> Var -> [Int] -> FOLForm
stUniform g (PrpBxA k) x _ | propPosNeg k g True = Negc (Eqdotc (VT x) (VT x))
                                    | propPosNeg k g False = Eqdotc (VT x) (VT x)
                                    | otherwise = undefined
stUniform g (NotBxA (NotBxA f)) x vars = stUniform g f x vars
stUniform h (NotBxA (ConBxA (NotBxA f) (NotBxA g))) x vars = Disjc (stUniform h f x vars : [stUniform h g x 
    (vars ++ varsInFOLform (stUniform h f x vars))])
stUniform h (ConBxA f g) x vars = Conjc (stUniform h f x vars : [stUniform h g x 
    (vars ++ varsInFOLform (stUniform h f x vars))])
stUniform h (NotBxA (Nbox n (NotBxA f))) (V x) vars = diamondsRMonoUniform h n vars x f
stUniform h (Nbox n f) (V x) vars = (\y -> Forallc [V y] 
    (Impc (boxedR n vars x y) 
        (stUniform h f (V y) (vars ++ getNthFresh n vars)))) (last (getNthFresh n vars))
stUniform _ TopBxA x _ = Eqdotc (VT x) (VT x)
stUniform h (NotBxA f) x vars = Negc (stUniform h f x vars)

diamondsRMonoUniform :: ModFormBxA -> Int -> [Int] -> Int -> ModFormBxA -> FOLForm
diamondsRMonoUniform h 0 vars x f = stUniform h f (V x) vars
diamondsRMonoUniform h n vars x f = Existsc (map V (getNthFresh n vars))
    (Conjc 
        (zipWith (\ y1 y2 -> Rc (VT (V y1)) (VT (V y2)))
            (x : init (getNthFresh n vars)) (getNthFresh n vars) 
            ++ [stUniform h f (V (last (getNthFresh n vars))) (vars ++ getNthFresh n vars)]
            ))

-- get BxA substitutions right away, to use in minimal instances
standTransBxAgBA :: ModFormBxA -> Var -> [Int] -> [(Int, Int -> FOLForm)] -> (FOLForm, [(Int, Int -> FOLForm)])
standTransBxAgBA (PrpBxA k) (V x) _ bxAs = (Pc k (VT (V x)), (k, Eqdotc (VT (V x)) . VT . V) : bxAs)
standTransBxAgBA (Nbox n (PrpBxA k)) (V x) vars bxAs = 
    (\y -> (Forallc [V y] 
    (Impc (boxedR n vars x y) 
        (Pc k (VT (V y)))), 
        bxAs ++ [(k, boxedR n vars x)]) ) (last (getNthFresh n vars))
standTransBxAgBA (NotBxA (NotBxA f)) x vars bxAs = standTransBxAgBA f x vars bxAs
standTransBxAgBA (ConBxA f g) x vars bxAs = (Conjc 
    (fst (standTransBxAgBA f x vars bxAs) : [fst (standTransBxAgBA g x 
    (vars ++ varsInFOLform (fst (standTransBxAgBA f x vars bxAs))) bxAs)]), 
    snd (standTransBxAgBA f x vars bxAs) ++ snd (standTransBxAgBA g x 
    (vars ++ varsInFOLform (fst (standTransBxAgBA f x vars bxAs))) bxAs))
standTransBxAgBA TopBxA x _ bxAs = (Eqdotc (VT x) (VT x), bxAs)
standTransBxAgBA (NotBxA (Nbox n (NotBxA f))) (V x) vars bxAs = (diamondsR n vars x f, 
    snd (standTransBxAgBA f (V (last (getNthFresh n vars))) (vars ++ getNthFresh n vars) bxAs))
standTransBxAgBA _ _ _ _= undefined 
