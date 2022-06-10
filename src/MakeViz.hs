{-#LANGUAGE OverloadedStrings#-}
module MakeViz where
import Data.GraphViz.Types.Monadic
import Data.GraphViz.Attributes
import Data.GraphViz.Types
import Data.GraphViz.Types.Generalised
import Languages
import Data.Bits

-- (Forallc [V 3] (Negc (Existsc [V 1,V 2] (Conjc [Rc (VT (V 0)) (VT (V 1)),Rc (VT (V 1)) (VT (V 2)),Rc (VT (V 2)) (VT (V 3))]))))
-- (Existsc [V 1] (Conjc [Rc (VT (V 0)) (VT (V 1)),Forallc [V 2] (Negc (Rc (VT (V 1)) (VT (V 2))))]))

-- each elem in output ((from, to), D (int), O (int), Eq (Bool), Neg (Bool)) list represents edge
-- when D (depth) is maximal : edge is dotted (new cluster)
-- when O (ors) not 0: Or case distintion, edge different colors (new cluster for every diff O value)
-- when Eq (equality) True: add 2 edges, equality 'node' in between, edges undirected, 'nodes' filled (no line around =)
-- when Neg (not possible): edges are red and filled
toClusters :: FOLFormVSAnt -> Int -> Int -> Bool -> [(([Char], [Char]), Int, Int, Bool, Bool)] -- (w_i,w_j), dotted/filled, color, eq (noDir)
toClusters Topc _ _ _ = undefined
toClusters (Pc _ _) _ _ _ = undefined
toClusters (Rc (VT (V k)) (VT (V j))) depth ors red = [(("w" ++ show k, "w" ++ show j), depth, ors, False, red)]
toClusters (Rc _ _) _ _ _ = undefined
toClusters (Eqdotc (VT (V k)) (VT (V j))) depth ors red = (("w" ++ show j, "="), depth, ors, True, red) : [(("w" ++ show k, "="), depth, ors, True, red)]
toClusters (Eqdotc _ _) _ _ _ = undefined
toClusters (Forallc _ f) depth ors red = toClusters f depth ors red
toClusters (Existsc _ f) depth ors red = toClusters f depth ors red
toClusters (Conjc []) _ _ _ = []
toClusters (Conjc (f:fs)) depth ors red = toClusters f depth ors red ++ toClusters (Conjc fs) depth ors red
toClusters (Disjc []) _ _ _ = []
toClusters (Disjc (f:fs)) depth ors red = toClusters f depth (ors + 1) red ++ toClusters (Conjc fs) depth (ors + 2) red
toClusters (Impc f g) depth ors red = toClusters f depth ors red ++ toClusters g (depth + 1) ors red
toClusters (Negc f) depth ors red = toClusters f depth ors (xor red True)

toClusters1 :: FOLFormVSAnt -> [(([Char], [Char]), Int, Int, Bool, Bool)]
toClusters1 f = toClusters f 0 0 False

toGraph :: [(([Char], [Char]), Int, Int, Int)] -> DotGraph String
toGraph = undefined