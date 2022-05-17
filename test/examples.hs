module Main (main) where

import Data.List
import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck (expectFailure,(===))

import FOLCorrespondent
import Languages
import ModalSimplify
import StandTrans
import FOLSimplify
import FOLSimplify (getEqVar)

main :: IO ()
main = hspec $ do
  describe "getting the pos/neg conjuncts (normal sq)" $ do
    describe "getPositiveBxA" $ do
      it "p & <>!p" $ getPositiveBxA (ConBxA (PrpBxA 0) (nDia 1 (NotBxA (PrpBxA 0)))) `shouldBe` PrpBxA 0
    it "getNegativeBxA" $
      getNegativeBxA (ConBxA (PrpBxA 0) (nDia 1 (NotBxA (PrpBxA 0)))) `shouldBe` NotBxA (Nbox 1 (PrpBxA 0))

    it "disjunct in antecedent gives conjunction of implications" $  -- 
      mainOperatorFOL (getFOLimp (NotBxA (ConBxA (NotBxA (Nbox 1 (PrpBxA 0))) (Nbox 2 (NotBxA (PrpBxA 0))))) (PrpBxA 0))
          `shouldBe` "Conjunction"

    it "getSqBxAbox functionally getSqBxa (but keeps track of variables)" $
        Just (getSqBxAbox (impBxA (nDia 2 (PrpBxA 1)) (PrpBxA 1)) 0 [0]) `shouldBe` getSqBxA (impBxA (nDia 2 (PrpBxA 1)) (PrpBxA 1))

    describe "splitting of disjuncts in Sq antecedent" $ do
      it "<><>([]p & ~q) | q " $
        length (splitOrAnt (toModBxA (modSimp (dis (dia (dia (Con (Box (Box (Prp 0))) (Not (Prp 1))))) (Prp 2))))) `shouldBe` 2
      it "(p0 | p1) & (p2 | p3) == (p0 & p2) | (p0 & p3) | (p1 & p2) | (p1 & p3)" $
        length (splitOrAnt (ConBxA (NotBxA (ConBxA (NotBxA (PrpBxA 0)) (NotBxA (PrpBxA 1)))) (NotBxA (ConBxA (NotBxA (PrpBxA 2)) (NotBxA (PrpBxA 3))))))
         `shouldBe` 4
      it "<><>(p | q) -> (<><>p | <><>q)" $
        length (splitOrAnt (NotBxA (Nbox 2 (ConBxA (NotBxA (PrpBxA 0)) (NotBxA (PrpBxA 1)))))) `shouldBe` 2
      it "(<><>([]p | ~q) | ~<>q) -> OR (<><>[]p, <><>~q, ~<>q) " $
        length (splitOrAnt (toModBxA (modSimp (dis (dia (dia (dis (Box (Prp 0)) (Not (Prp 1))))) (Not (dia (Prp 1))))))) `shouldBe` 3
      it "~(p&q) == ~p | ~q " $
        length (splitOrAnt (toModBxA (modSimp (Not (Con (Prp 0) (Prp 1)))))) `shouldBe` 2

    describe "get used variables in FOL form " $ do
      it "6 box/dia (in antecedent) -> 7 variables" $
        sort (varsInFOLform2 (stTrAnt (impBxA (ConBxA (nDia 2 (Nbox 2 (PrpBxA 0))) (ConBxA (nDia 1 (PrpBxA 1)) (Nbox 1 (PrpBxA 2))))
         (nDia 1 (disBxA (PrpBxA 0) (Nbox 2 (PrpBxA 1))))))) `shouldBe` [0..6]

    describe "get substitution of predicate, disj. of when occurs as(boxed) atom in antecedent" $ do
      it "P0 occurs 2 times in antecedent" $
        elemsInDisj (getSubstitution 0 (subsAnt (impBxA (ConBxA (Nbox 2 (PrpBxA 0)) (PrpBxA 0)) (nDia 1 (PrpBxA  0)))) 3) `shouldBe` 2

    describe "simplifying Exists Vi Conj [Vi = Vj, ...]"  $ do
      it "in: 2 [Rx1x2, x1=x2], out: (Just) 1" $ getEqVar 2 [Rc (VT (V 1)) (VT (V 2)), Eqdotc (VT (V 1)) (VT (V 2))] `shouldBe` Just 1

-- functions for testing

mainOperatorFOL :: FOLFormVSAnt -> String
mainOperatorFOL Topc = "Top"
mainOperatorFOL (Pc _ _) = "Predicate"
mainOperatorFOL (Rc _ _) = "Relation"
mainOperatorFOL (Eqdotc _ _) = "Equation"
mainOperatorFOL (Negc _) = "Negation"
mainOperatorFOL (Conjc _) = "Conjunction"
mainOperatorFOL (Disjc _) = "Disjunction"
mainOperatorFOL (Impc _ _) = "Implication"
mainOperatorFOL (Forallc _ _) = "Universal Quantifier"
mainOperatorFOL (Existsc _ _) = "Existential Quantifier"

elemsInDisj :: FOLFormVSAnt -> Int
elemsInDisj (Disjc f) = length f
elemsInDisj _ = undefined