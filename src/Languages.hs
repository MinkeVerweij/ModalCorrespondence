-- MODAL LOGIC
module Languages where
-- import Stand_trans (getFresh)
import Data.List


type World = Integer
type Universe = [World]
type Proposition = Int
type Valuation = World -> [Proposition]
type Relation = [(World,World)]
data KripkeModel = KrM Universe Valuation Relation

data ModForm = Prp Proposition
             | Not ModForm
             | Con ModForm ModForm
             | Box ModForm
             | Top
             deriving (Eq,Ord,Show)

dia :: ModForm -> ModForm
dia f = Not (Box (Not f))

dis :: ModForm -> ModForm -> ModForm
dis f g = Not (Con (Not f) (Not g))

imp :: ModForm -> ModForm -> ModForm
imp f g = Not (Con f (Not g))

bot :: ModForm
bot = Not Top

type N = Int 

data ModFormBxA =
            --  Nbox N Proposition
            PrpBxA Proposition
             | NotBxA ModFormBxA
             | ConBxA ModFormBxA ModFormBxA
            --  | Ndia N Proposition
             | Ndia N ModFormBxA
             | TopBxA
             deriving (Eq,Ord,Show)

-- diaBxA :: ModFormBxA -> ModFormBxA
-- diaBxA f = NotBxA (BoxBxA (NotBxA f))

nBox :: Int -> ModFormBxA -> ModFormBxA
nBox n f = NotBxA (Ndia n (NotBxA f))

disBxA :: ModFormBxA -> ModFormBxA -> ModFormBxA
disBxA f g = NotBxA (ConBxA (NotBxA f) (NotBxA g))

impBxA :: ModFormBxA -> ModFormBxA -> ModFormBxA
impBxA f g = NotBxA (ConBxA f (NotBxA g))

botBxA :: ModFormBxA
botBxA = NotBxA TopBxA


-- FOL 1 (2 term conjuncts + primitive)
newtype Var = V Int deriving(Eq, Ord, Show)

data Term = VT Var | C Int deriving(Eq, Ord, Show)

data FOLForm = P Int Term | R Term Term | Eqdot Term Term |
                Neg FOLForm | Conj FOLForm FOLForm |
                Forall Var FOLForm 
                deriving(Eq, Ord, Show)


-- | Exists Var FOLForm
disj :: FOLForm -> FOLForm -> FOLForm
disj f g = Neg (Conj (Neg f) (Neg g))

impl :: FOLForm -> FOLForm -> FOLForm
impl f g = Neg (Conj f (Neg g))

-- boxedR1 :: FOLForm -> [Int] -> (Int -> FOLForm)
-- boxedR1 (P k t) _ = Eqdot t . VT . V
-- boxedR1 (Forall  f) vars =


-- FOL 2 (list conj. + non-primitive)
data FOLFormVSAnt = Pc Int Term | Rc Term Term | Eqdotc Term Term |
                    Negc FOLFormVSAnt | 
                    Conjc [FOLFormVSAnt] |
                    Impc FOLFormVSAnt FOLFormVSAnt | 
                    Disjc [FOLFormVSAnt] |
                    Forallc [Var] FOLFormVSAnt |
                    Existsc [Var] FOLFormVSAnt |
                    Topc
                    deriving(Eq, Ord, Show)

getFresh :: [Int] -> Int
getFresh li = head ([0..] \\ li)

getNthFresh :: Int -> [Int] -> [Int]
getNthFresh 0 li = [getFresh li]
getNthFresh n li = take n ([0..] \\ li)

-- boxedR :: Int -> [Int] -> Int -> (Int -> FOLFormVSAnt)
-- -- boxedR 0 vars x = (\y -> Eqdotc (VT (V x)) (VT (V y))) (getFresh vars)
-- boxedR 0 _ x = Eqdotc (VT (V x)) . VT . V
-- boxedR 1 _ x = Rc (VT (V x)) . VT . V
-- boxedR n vars x = \y -> Existsc (map V (getNthFresh (n -1) vars)) 
--     (Conjc (zipWith (\ y1 y2 -> Rc (VT (V y1)) (VT (V y2))) 
--         (x : getNthFresh (n-1) vars) (getNthFresh (n - 1) vars ++ [y]))
--         )
boxedR :: Int -> [Int] -> Int -> (Int -> FOLFormVSAnt)
-- boxedR 0 vars x = (\y -> Eqdotc (VT (V x)) (VT (V y))) (getFresh vars)
boxedR 0 _ x y = (Eqdotc (VT (V x)) . VT . V) y
boxedR 1 _ x y = Rc (VT (V x))  (VT (V y))
boxedR n vars x y = Existsc (map V (getNthFresh (n -1) vars)) 
    (Conjc (zipWith (\ y1 y2 -> Rc (VT (V y1)) (VT (V y2))) 
        (x : getNthFresh (n-1) vars) (getNthFresh (n - 1) vars ++ [y]))
        )

-- diamondsR :: Int -> [Int] -> Int -> ModFormBxA -> FOLFormVSAnt
-- diamondsR 0 vars _ _ = (Eqdotc (VT (V x)) . VT . V) (getFresh vars)
-- -- diamondsR n vars x f = Existsc (map V (getNthFresh n vars))
-- --     (Conjc 
-- --         (zipWith (\ y1 y2 -> Rc (VT (V y1)) (VT (V y2)))
-- --             (x : init (getNthFresh n vars)) (getNthFresh n vars) 
-- --             ++ [f (last (getNthFresh n vars))]
-- --             ))
-- diamondsR n vars x (PrpBxA k) = Existsc (map V (getNthFresh n vars))
--     (Conjc 
--         (zipWith (\ y1 y2 -> Rc (VT (V y1)) (VT (V y2)))
--             (x : init (getNthFresh n vars)) (getNthFresh n vars) 
--             ++ [(Pc k . VT . V) (last (getNthFresh n vars))]
--             ))
-- diamondsR n vars x (PrpBxA k) = Existsc (map V (getNthFresh n vars))
--     (Conjc 
--         (zipWith (\ y1 y2 -> Rc (VT (V y1)) (VT (V y2)))
--             (x : init (getNthFresh n vars)) (getNthFresh n vars) 
--             ++ [(Pc k . VT . V) (last (getNthFresh n vars))]
--             ))
-- diamondsR 1 = boxedR 1
-- diamondsR n vars x = \y -> Existsc


-- boxedR :: Int -> [Int] -> Int -> FOLFormVSAnt
-- -- boxedR 0 vars x = (\y -> Eqdotc (VT (V x)) (VT (V y))) (getFresh vars)
-- boxedR 0 vars x = (Eqdotc (VT (V x)) . VT . V) (getFresh vars)
-- boxedR 1 vars x = (Rc (VT (V x)) . VT . V) (getFresh vars)
-- boxedR n vars x = Existsc (map V (getNthFresh (n -1) vars)) 
--     (Conjc (zipWith (\ y1 y2 -> Rc (VT (V y1)) (VT (V y2))) 
--         (x : getNthFresh (n-1) vars) (getNthFresh n vars)))

-- boxedR n vars x = Existsc (map V (getNthFresh n vars)) (Conjc (map (\(y1, y2) -> (Rc (VT (V y1)) (VT (V y2)))) (zip (getNthFresh (n + 1) vars) (x : getNthFresh n vars))))
-- boxedR n vars x = Existsc (getNthFresh n vars) (Conjc map )
-- boxedR n vars x = Existsc (getNthFresh n vars) Conjc map (\y1 -> Rc (VT (V y1)) (. VT . V) (getNthFresh (n + 1) vars)) x : getNthFresh n vars
-- boxedR n vars = Existsc (getNthFresh n vars) Conjc map (\y1 -> (\y2 -> (Rc (VT (V y1)) (VT (V y2)))) (getNthFresh (n + 1) vars)) x : (getNthFresh n vars)

boxedR_t :: [FOLFormVSAnt]
boxedR_t = [
    (boxedR 0 [0,1] 0) 9,
    (boxedR 1 [0] 0) 9,
    (boxedR 8 [0] 0) 99
    ]