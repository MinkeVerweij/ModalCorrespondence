module FOLSimplify where

import Languages

-- STILL TO DO: take step back, simplify until no changes
simpFOL :: FOLFormVSAnt -> FOLFormVSAnt
simpFOL (Negc (Negc f)) = simpFOL f
simpFOL (Conjc []) = Topc
simpFOL (Conjc [f]) = simpFOL f
simpFOL (Disjc []) = Negc Topc
simpFOL (Disjc [f]) = simpFOL f
simpFOL (Disjc fs) | Topc `elem` fs = Topc
                | otherwise = Disjc (map simpFOL fs)
simpFOL (Impc Topc g) = simpFOL g
simpFOL (Impc f g) = Impc (simpFOL f) (simpFOL g)
simpFOL (Negc f) = Negc (simpFOL f)

simpFOL (Forallc [] f) = simpFOL f
simpFOL f = f