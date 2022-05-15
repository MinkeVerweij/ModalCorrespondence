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
getBoxedn (Not (Not (Box f))) n = getBoxedn f (n+1) 
getBoxedn f n = (n, toModBxA f)

boxModSimp :: ModFormBxA -> ModFormBxA
boxModSimp (PrpBxA k) = PrpBxA k
boxModSimp TopBxA = TopBxA
boxModSimp (NotBxA (NotBxA f)) = f
boxModSimp (NotBxA (Nbox n (NotBxA (NotBxA f)))) = NotBxA (Nbox n (boxModSimp f)) -- <>~

boxModSimp (ConBxA TopBxA f) = boxModSimp f
boxModSimp (ConBxA f TopBxA) = boxModSimp f

boxModSimp (NotBxA (ConBxA (NotBxA (NotBxA f)) (NotBxA (NotBxA g)))) = NotBxA (ConBxA (boxModSimp f) (boxModSimp g))
boxModSimp (NotBxA (ConBxA (NotBxA (NotBxA f)) g)) = NotBxA (ConBxA (boxModSimp f) (boxModSimp g))
boxModSimp (NotBxA (ConBxA f (NotBxA (NotBxA g)))) = NotBxA (ConBxA (boxModSimp f) (boxModSimp g))

boxModSimp (NotBxA f) = NotBxA (boxModSimp f)
boxModSimp (ConBxA f g) = ConBxA (boxModSimp f) (boxModSimp g)

boxModSimp (Nbox n (Nbox m f)) = Nbox (n+m) (boxModSimp f)
boxModSimp (Nbox n (NotBxA (NotBxA (Nbox m f)))) = Nbox (n+m) (boxModSimp f)
boxModSimp (Nbox n f) = Nbox n (boxModSimp f)