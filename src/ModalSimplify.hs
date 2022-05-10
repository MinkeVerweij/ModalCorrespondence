module ModalSimplify where
import Languages

modSimp :: ModForm -> ModForm -- eliminate double neg: ~~f = f 
modSimp (Prp k) = Prp k
modSimp Top = Top
modSimp (Not (Not f)) = f
modSimp (Not (Box (Not (Not f)))) = Not (Box (modSimp f)) -- <>~

modSimp (Not (Con (Not (Not f)) (Not (Not g)))) = Not (Con (modSimp f) (modSimp g))
modSimp (Not (Con (Not (Not f)) g)) = Not (Con (modSimp f) (modSimp g))
modSimp (Not (Con f (Not (Not g)))) = Not (Con (modSimp f) (modSimp g))

modSimp (Not f) = Not (modSimp f)
modSimp (Con f g) = Con (modSimp f) (modSimp g)
modSimp (Box f) = Box (modSimp f)

toModBxA :: ModForm -> ModFormBxA
toModBxA (Box f) = uncurry Nbox (getBoxedn f 1)
toModBxA (Prp k) = PrpBxA k
toModBxA Top = TopBxA
-- toModBxA (Not (Not f)) = f
-- toModBxA (Not (Box (Not (Not f)))) = Not (Box (toModBxA f)) -- <>~

-- toModBxA (Not (Con (Not (Not f)) (Not (Not g)))) = NotBxA (ConBxA (toModBxA f) (toModBxA g))
toModBxA (Not (Con (Not (Not f)) g)) = NotBxA (ConBxA (toModBxA f) (toModBxA g))
toModBxA (Not (Con f (Not (Not g)))) = NotBxA (ConBxA (toModBxA f) (toModBxA g))

toModBxA (Not f) = NotBxA (toModBxA f)
toModBxA (Con f g) = ConBxA (toModBxA f) (toModBxA g)
-- toModBxA (Box f) = BoxBxA (toModBxA f)

getBoxedn :: ModForm -> Int -> (Int, ModFormBxA)
getBoxedn (Box f) n = getBoxedn f (n+1)
getBoxedn f n = (n, toModBxA f)
