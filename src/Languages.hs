-- MODAL LOGIC
module Languages where
-- import Stand_trans (getFresh)
import Data.List

type Proposition = Int

-- 'normal' modal formulas (primitive)
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

biImp :: ModForm -> ModForm -> ModForm
biImp f g = Con (imp f g) (imp g f)

bot :: ModForm
bot = Not Top

-- print modal formulas nicely in terminal
ppModForm :: ModForm -> String
ppModForm Top = "T"
ppModForm (Not Top) = "⊥"
ppModForm (Prp 0) = "p"
ppModForm (Prp 1) = "q"
ppModForm (Prp 2) = "r"
ppModForm (Prp i) = "p" ++ show i
ppModForm (Not (Box (Not f))) = "♢" ++ ppModForm f
ppModForm (Not (Con (Not f) (Not g))) = "( " ++ ppModForm f ++ " ∨ " ++ ppModForm g ++ " )"
ppModForm (Not (Con f (Not g))) = "( " ++ ppModForm f ++ " → " ++ ppModForm g ++ " )"
ppModForm (Con f g) = "( " ++ ppModForm f ++ " ∧ " ++ ppModForm g ++ " )"
ppModForm (Box f) = "□" ++ ppModForm f
ppModForm (Not f) = "¬" ++ ppModForm f


-- Modal Formulas with Boxed atoms as primitives
type N = Int 

data ModFormBxA =
            PrpBxA Proposition
             | NotBxA ModFormBxA
             | ConBxA ModFormBxA ModFormBxA
             | Nbox N ModFormBxA
             | TopBxA
             deriving (Eq,Ord,Show)

nDia :: Int -> ModFormBxA -> ModFormBxA
nDia n f = NotBxA (Nbox n (NotBxA f))

disBxA :: ModFormBxA -> ModFormBxA -> ModFormBxA
disBxA f g = NotBxA (ConBxA (NotBxA f) (NotBxA g))

impBxA :: ModFormBxA -> ModFormBxA -> ModFormBxA
impBxA f g = NotBxA (ConBxA f (NotBxA g))

botBxA :: ModFormBxA
botBxA = NotBxA TopBxA


newtype Var = V Int deriving(Eq, Ord, Show)

data Term = VT Var | C Int deriving(Eq, Ord, Show)

ppTerm :: Term -> String
ppTerm (VT (V i)) | i == 0 = "x"
                | otherwise = "x_" ++ show i
ppTerm (C i) = "c_" ++ show i

-- FOL 2 (list conj. + non-primitive)
data FOLForm = Pc Int Term | Rc Term Term | Eqdotc Term Term |
                    Negc FOLForm | 
                    Conjc [FOLForm] |
                    Impc FOLForm FOLForm | 
                    Disjc [FOLForm] |
                    Forallc [Var] FOLForm |
                    Existsc [Var] FOLForm |
                    Topc
                    deriving(Eq, Ord, Show)

-- print FOL nicely in terminal
ppFOLForm :: FOLForm -> String
ppFOLForm Topc = "T"
ppFOLForm (Negc Topc) = "⊥"
ppFOLForm (Pc i t) = "P_" ++ show i ++ " " ++ ppTerm t
ppFOLForm (Rc t1 t2) = "R " ++ ppTerm t1 ++ " " ++ ppTerm t2
ppFOLForm (Eqdotc t1 t2) = ppTerm t1 ++ " = " ++ ppTerm t2
ppFOLForm (Negc f) = "¬" ++ ppFOLForm f
ppFOLForm (Conjc fs) = "AND {" ++ intercalate ", " (map ppFOLForm fs) ++ "}"
ppFOLForm (Impc f1 f2) = "(" ++ ppFOLForm f1 ++ " → " ++ ppFOLForm f2 ++ ")"
ppFOLForm (Disjc fs) = "OR {" ++ intercalate "," (map ppFOLForm fs) ++ "}"
ppFOLForm (Forallc [] f) = ppFOLForm f
ppFOLForm (Forallc ((V i):xs) f) = "∀x_" ++ show i ++ " " ++ ppFOLForm (Forallc xs f)
ppFOLForm (Existsc [] f) = ppFOLForm f
ppFOLForm (Existsc ((V i):xs) f) = "∃x_" ++ show i ++ " " ++ ppFOLForm (Existsc xs f)

isConj :: FOLForm -> Bool
isConj (Conjc _) = True
isConj _ = False

isDisj :: FOLForm -> Bool
isDisj (Disjc _) = True
isDisj _ = False

-- get 1 fresh variable
getFresh :: [Int] -> Int
getFresh li = head ([0..] \\ li)

-- get n fresh variables
getNthFresh :: Int -> [Int] -> [Int]
getNthFresh 0 li = [getFresh li]
getNthFresh n li = take n ([0..] \\ li)

-- boxed R as defined in book
boxedR :: Int -> [Int] -> Int -> (Int -> FOLForm)
boxedR 0 _ x y = (Eqdotc (VT (V x)) . VT . V) y
boxedR 1 _ x y = Rc (VT (V x))  (VT (V y))
boxedR n vars x y = Existsc (map V (getNthFresh (n -1) vars)) 
    (Conjc (zipWith (\ y1 y2 -> Rc (VT (V y1)) (VT (V y2))) 
        (x : getNthFresh (n-1) vars) (getNthFresh (n - 1) vars ++ [y]))
        )
