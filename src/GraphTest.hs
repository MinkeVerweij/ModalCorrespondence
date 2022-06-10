{-#LANGUAGE OverloadedStrings#-}
module GraphTest where
import Data.GraphViz.Types.Monadic
import Data.GraphViz.Attributes
import Data.GraphViz.Types
import Data.GraphViz.Types.Generalised


reflexivity :: DotGraph String -- Rc (VT (V 0)) (VT (V 0))
reflexivity = digraph (Str "G") $ do
    -- cluster (Num (Int 0)) $ do
        graphAttrs [style solid, color White]
        nodeAttrs [shape Circle] -- otherwise oval
        edgeAttrs [style dotted, color Black]
        "w" --> "w"

-- (Forallc [V 1,V 2] (Impc (Conjc [Rc (VT (V 0)) (VT (V 1)),Rc (VT (V 1)) (VT (V 2))]) (Rc (VT (V 0)) (VT (V 2)))))
transitivity :: DotGraph String 
transitivity = digraph (Str "G") $ do
    nodeAttrs [shape Circle]
    graphAttrs [style solid, color White]
    
    cluster (Num (Int 0)) $ do
        edgeAttrs [style solid, color Black]
        "w" --> "w1"
        "w1" --> "w2"
    cluster (Num (Int 1)) $ do
        edgeAttrs [style dotted, color Black]
        "w" --> "w2"

-- Forallc [V 1] (Impc (Rc (VT (V 0)) (VT (V 1))) (Existsc [V 2] (Conjc [Rc (VT (V 0)) (VT (V 2)),Rc (VT (V 2)) (VT (V 1))])))
density :: DotGraph String
density = digraph (Str "G") $ do
    nodeAttrs [shape Circle]
    graphAttrs [style solid, color White]

    cluster (Num (Int 0)) $ do
        edgeAttrs [style solid, color Black]
        "w" --> "w1"
    cluster (Num (Int 1)) $ do
        edgeAttrs [style dotted, color Black]
        "w" --> "w2"
        "w2" --> "w1"

-- []p->[]<>p == ∀x_1 (R x_0 x_1 → ∀x_3 (R x_0 x_3 → ∃x_4 AND {R x_3 x_4, R x_1 x_4}))
-- Forallc [V 1] (Impc (Rc (VT (V 0)) (VT (V 1))) (Forallc [V 3] (Impc (Rc (VT (V 0)) (VT (V 3))) (Existsc [V 4] (Conjc [Rc (VT (V 3)) (VT (V 4)),Rc (VT (V 1)) (VT (V 4))])))))
churchRosser :: DotGraph String
churchRosser = digraph (Str "G") $ do
    nodeAttrs [shape Circle]
    graphAttrs [style solid, color White]

    cluster (Num (Int 0)) $ do
        edgeAttrs [style solid, color Black]
        "w" --> "w1"

    cluster (Num (Int 1)) $ do
        edgeAttrs [style solid, color Black]
        "w" --> "w3"

    cluster (Num (Int 2)) $ do
        edgeAttrs [style dotted, color Black]
        "w3" --> "w4"
        "w1" --> "w4"

-- (p&<><>p) -> <>p == ∀x_1 ∀x_2 (AND {R x_0 x_1, R x_1 x_2} → OR {R x_0 x_0,R x_0 x_2})
-- (Forallc [V 1,V 2] (Impc (Conjc [Rc (VT (V 0)) (VT (V 1)),Rc (VT (V 1)) (VT (V 2))]) (Disjc [Rc (VT (V 0)) (VT (V 0)),Rc (VT (V 0)) (VT (V 2))])))
withDisj :: DotGraph String
withDisj = digraph (Str "G") $ do
    nodeAttrs [shape Circle]
    graphAttrs [style solid, color White]
    cluster (Num (Int 0)) $ do
        edgeAttrs [style solid, color Black]
        "w" --> "w1"
        "w1" --> "w2"
    cluster (Num (Int 1)) $ do
        edgeAttrs [style dotted, color Green]
        "w" --> "w"
    cluster (Num (Int 2)) $ do
        edgeAttrs [style dotted, color Green4]
        "w" --> "w2"

-- <>p->[]p == ∀x_1 (R x_0 x_1 → ∀x_2 (R x_0 x_2 → x_1 = x_2))
-- Forallc [V 1] (Impc (Rc (VT (V 0)) (VT (V 1))) (Forallc [V 2] (Impc (Rc (VT (V 0)) (VT (V 2))) (Eqdotc (VT (V 1)) (VT (V 2))))))
withEq :: DotGraph String
withEq = digraph (Str "G") $ do
    nodeAttrs [shape Circle]
    graphAttrs [style solid, color White]
    cluster (Num (Int 0)) $ do
        edgeAttrs [style solid, color Black]
        "w" --> "w1" 
    cluster (Num (Int 1)) $ do
        edgeAttrs [style solid, color Black]
        "w" --> "w2"
    cluster (Num (Int 2)) $ do
        -- graphAttrs [style solid, color White, noArrow]
        edgeAttrs [style dotted, color Black, edgeEnds NoDir]
        nodeAttrs [style filled, color White]
        "w1" --> "="
        "=" --> "w2"

-- (<>p&<><>p)->p == ∀x_1 ∀x_2 ∀x_3 (AND {R x_0 x_1, R x_0 x_2, R x_2 x_3} → OR {x_1 = x_0,x_3 = x_0})
-- (Forallc [V 1,V 2,V 3] (Impc (Conjc [Rc (VT (V 0)) (VT (V 1)),Rc (VT (V 0)) (VT (V 2)),Rc (VT (V 2)) (VT (V 3))]) (Disjc [Eqdotc (VT (V 1)) (VT (V 0)),Eqdotc (VT (V 3)) (VT (V 0))])))
withDisjEq :: DotGraph String
withDisjEq = digraph (Str "G") $ do
    nodeAttrs [shape Circle]
    graphAttrs [style solid, color White]
    cluster (Num (Int 0)) $ do
        edgeAttrs [style solid, color Black]
        "w" --> "w1"
        "w" --> "w2"
        "w2" --> "w3"
    cluster (Num (Int 1)) $ do
        edgeAttrs [style dotted, color Green, edgeEnds NoDir]
        nodeAttrs [style filled, color White]
        "w" --> "="
        "w1" --> "="
    cluster (Num (Int 2)) $ do
        edgeAttrs [style dotted, color DarkGreen, edgeEnds NoDir]
        nodeAttrs [style filled, color White]
        "w" --> "="
        "w3" --> "="

-- []p == ∀x_1 ¬R x_0 x_1
-- Forallc [V 1] (Negc (Rc (VT (V 0)) (VT (V 1))))
withNeg :: DotGraph String
withNeg = digraph (Str "G") $ do
    nodeAttrs [shape Circle]
    graphAttrs [style solid, color White]
    cluster (Num (Int 0)) $ do
        edgeAttrs [style dotted, color Red]
        "w" --> "w1" 

example :: DotGraph String
example = digraph (Str "G") $ do

   cluster (Num (Int 0)) $ do
       graphAttrs [style filled, color LightGray]
       nodeAttrs [style filled, color White]
       "a0" --> "a1"
       "a1" --> "a2"
       "a2" --> "a3"
       graphAttrs [textLabel "process #1"]

   cluster (Num (Int 1)) $ do
       nodeAttrs [style filled]
       "b0" --> "b1"
       "b1" --> "b2"
       "b2" --> "b3"
       graphAttrs [textLabel "process #2", color Blue]

   "start" --> "a0"
   "start" --> "b0"
   "a1" --> "b3"
   "b2" --> "a3"
   "a3" --> "end"
   "b3" --> "end"

   node "start" [shape MDiamond]
   node "end" [shape MSquare]