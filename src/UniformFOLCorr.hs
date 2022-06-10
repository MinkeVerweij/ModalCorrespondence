module UniformFOLCorr where
import Languages
import StandTrans
import SahlqvistCheck
import FOLSimplify
import Data.List

getFOLuniform :: ModFormBxA -> FOLFormVSAnt
getFOLuniform f = simpFOL3 (standTransBxAUniform f f (V 0) [0])

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

xor :: Bool -> Bool -> Bool
xor True False = True
xor False True = True
xor _ _ = False

isUniform:: ModFormBxA -> Bool
isUniform f = all  (`propUniform` f) (nub (props f))

propUniform :: Int -> ModFormBxA -> Bool
propUniform k f = propPosNeg  k f True || propPosNeg  k f False

-- if Prp k occurs pos in f: propPosNeg k f True --> True
-- if Prp k occurs neg in f: propPosNeg k f False --> True
propPosNeg :: Int -> ModFormBxA -> Bool -> Bool
propPosNeg  _ TopBxA _ = True
propPosNeg  _ (PrpBxA _) c = c
propPosNeg  k (NotBxA f) c | k `elem` props f =  propPosNeg  k f (c `xor` True)
                            | otherwise = c
propPosNeg  k (ConBxA f g) c | k `elem` props f && k `elem` props g = propPosNeg  k f c && propPosNeg  k g c
        | k `elem` props f = propPosNeg k f c
        | k `elem` props g = propPosNeg k g c
        | otherwise = c
propPosNeg  k (Nbox _ f) c = propPosNeg  k f c
