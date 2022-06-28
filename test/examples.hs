module Main (main) where

import Data.List
import Test.Hspec
-- import Test.Hspec.QuickCheck
-- import Test.QuickCheck (expectFailure,(===))

import FOLCorrespondent
import ModalSimplify
import StandTrans
import FOLSimplify
import Instantiation
import SahlqvistCheck
import Data.Maybe
import Languages

main :: IO ()
main = hspec $ do
  describe "determining whether form pos/neg" $ do
      it "(q & (p & ~[]p)) neg" $ isNegativeBxA (ConBxA (PrpBxA 1) (ConBxA (PrpBxA 0) (nDia 1 (NotBxA (PrpBxA 0))))) `shouldBe` False
      it "(q & (p & ~[]p)) pos" $ isNegativeBxA (NotBxA (ConBxA (PrpBxA 1) (ConBxA (PrpBxA 0) (nDia 1 (NotBxA (PrpBxA 0)))))) `shouldBe` False
      it "(p & ~[]p) neg " $ isNegativeBxA (ConBxA (PrpBxA 0) (nDia 1 (NotBxA (PrpBxA 0)))) `shouldBe` False
      it "(p & ~[]p) pos" $ isNegativeBxA (NotBxA (ConBxA (PrpBxA 0) (nDia 1 (NotBxA (PrpBxA 0))))) `shouldBe` False

      
    
  describe "getting the pos/neg conjuncts (normal sq)" $ do
    describe "getPositiveBxA" $ do
      it "p & <>~p" $ getPositiveBxA (ConBxA (PrpBxA 0) (nDia 1 (NotBxA (PrpBxA 0)))) `shouldBe` PrpBxA 0
      it "(q & (p & ~[]p))" $ getPositiveBxA (ConBxA (PrpBxA 1) (ConBxA (PrpBxA 0) (nDia 1 (NotBxA (PrpBxA 0))))) `shouldBe` ConBxA (PrpBxA 1) (PrpBxA 0)
    describe "getNegativeBxA" $ do
      it "p & <>~p" $ getNegativeBxA (ConBxA (PrpBxA 0) (nDia 1 (NotBxA (PrpBxA 0)))) `shouldBe` NotBxA (Nbox 1 (PrpBxA 0))
      it "(q & (p & ~[]p))" $ getNegativeBxA (ConBxA (PrpBxA 1) (ConBxA (PrpBxA 0) (nDia 1 (NotBxA (PrpBxA 0))))) `shouldBe` NotBxA (Nbox 1 (PrpBxA 0))

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
        length (splitOrAnt (toModBxA (modSimp (dis (dia (dia (dis (Box (Prp 0)) (Not (Prp 0))))) (Not (dia (Prp 1))))))) `shouldBe` 3
      it "~(p&q) == ~p | ~q " $
        length (splitOrAnt (toModBxA (modSimp (Not (Con (Prp 0) (Prp 1)))))) `shouldBe` 2
      it "<>((p&<>p)|~q)" $
        length (splitOrAnt (toModBxA (modSimp (dia (dis (Con (Prp 0) (dia (Prp 0))) (Not (Prp 1))))))) `shouldBe` 2

        -- splitOrAnt (toModBxA (modSimp (Not (dia (dis (Prp 0) (Prp 1))))))

    describe "get used variables in FOL form " $ do
      it "6 box/dia (in antecedent) -> 7 variables" $
        sort (varsInFOLform (standTransAnt (impBxA (ConBxA (nDia 2 (Nbox 2 (PrpBxA 0))) (ConBxA (nDia 1 (PrpBxA 1)) (Nbox 1 (PrpBxA 2))))
         (nDia 1 (disBxA (PrpBxA 0) (Nbox 2 (PrpBxA 1))))))) `shouldBe` [0..6]

    describe "get substitution of predicate, disj. of when occurs as(boxed) atom in antecedent" $ do
      it "P0 occurs 2 times in antecedent" $
        elemsInDisj (getSubstitution 0 (getSubstitutionsFromAnt (impBxA (ConBxA (Nbox 2 (PrpBxA 0)) (PrpBxA 0)) (nDia 1 (PrpBxA  0)))) 3) `shouldBe` 2

    describe "simplifying Exists Vi Conj [Vi = Vj, ...]"  $ do
      it "in: 2 [Rx1x2, x1=x2], out: (Just) 1" $ getEqVar 2 [Rc (VT (V 1)) (VT (V 2)), Eqdotc (VT (V 1)) (VT (V 2))] `shouldBe` Just 1

    describe "Has FOL (Sahlqvist) correspondent" $ do
      it "reflexivity Y" $ getSqBxA1 (toModBxA (modSimp (imp (Box (Prp 0)) (Prp 0)))) `shouldBe` Just (Rc (VT (V 0)) (VT (V 0)))
      it "boxed reflexivity Y" $ isJust (getSqBxA1 (toModBxA (modSimp (Box (Box (Box (Box (Box (Box (Box (Box (Box (Box (imp (Box (Prp 0)) (Prp 0))))))))))))))) `shouldBe` True 
      it "McKinsey N" $ isJust (getSqBxA1 (toModBxA (modSimp (imp (Box (dia (Prp 0))) (dia (Box (Prp 0))))))) `shouldBe` False
      it "[] McKinsey & transitivity N" $ isJust (getSqBxA1 (toModBxA (modSimp (Con (imp (Box (dia (Prp 0))) (dia (Box (Prp 0)))) (imp (dia (dia (Prp 1))) (dia (Prp 1))))))) `shouldBe` False
      it "Lob N" $ isJust (getSqBxA1 (toModBxA (modSimp (imp (Box (imp (Box (Prp 0)) (Prp 0))) (Box (Prp 0)))))) `shouldBe` False
      it "~[]<>p not Sq" $ isSqBxA (toModBxA (modSimp (Not (Box (dia (Prp 0))))) ) `shouldBe` False
      it "~([]<>p&<>[]p)" $ isSqBxA (toModBxA (modSimp (Not (Con (Box (dia (Prp 0))) (dia (Box (Prp 0))))))) `shouldBe` False
      it "([]<>p|<>[]p)" $ isSqBxA (toModBxA (modSimp  (dis (Box (dia (Prp 0))) (dia (Box (Prp 0)))))) `shouldBe` True
      it "[]p->p not uniform" $ isUniform (toModBxA (modSimp (imp (Box (Prp 0)) (Prp 0)))) `shouldBe` False
      it "~[]<>p & ([]p->p) has corresp." $ isJust (getSqBxA (toModBxA (modSimp (Con (Not (Box (dia (Prp 0)))) (imp (Box (Prp 0)) (Prp 0)))))) `shouldBe` True


-- functions for testing

mainOperatorFOL :: FOLForm -> String
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

elemsInDisj :: FOLForm -> Int
elemsInDisj (Disjc f) = length f
elemsInDisj _ = undefined