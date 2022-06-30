{-#LANGUAGE OverloadedStrings#-}
module MakeViz where
import Data.GraphViz.Types.Monadic
import Data.GraphViz.Attributes
import Data.GraphViz.Types.Generalised
import Languages
import Data.Bits
import Data.List
import Data.GraphViz (ToGraphID(toGraphID))
import FOLSimplify

-- preliminary check for visualization (not too many nested clusters)
clusterDepth :: FOLForm -> Int -> Int
clusterDepth (Conjc fs) n | hasForAllImp fs = (maximum [clusterDepth f n | f <- fs ]) + 1
                            | otherwise = n
clusterDepth (Disjc fs) n | hasForAllImp fs = (maximum [clusterDepth f n | f <- fs ]) + 1
                            | otherwise = n
clusterDepth (Existsc _ (Conjc fs)) n | hasForAllImp fs = (maximum [clusterDepth f n | f <- fs ]) + 1
                            | otherwise = n
clusterDepth (Existsc _ (Disjc fs)) n | hasForAllImp fs = (maximum [clusterDepth f n | f <- fs ]) + 1
                            | otherwise = n
clusterDepth (Forallc _ (Disjc fs)) n 
    | hasForAllImp fs = (maximum [clusterDepth f n | f <- fs ]) + 1
    | otherwise = n
clusterDepth (Forallc _ (Existsc _ (Conjc fs))) n
    | hasForAllImp fs = (maximum [clusterDepth f n | f <- fs ]) + 1
    | otherwise = n
clusterDepth _ n = n

-- preliminary check for visualization (not too implied ors)
impliedOrs :: FOLForm -> Bool
impliedOrs (Impc _ (Disjc fs)) | length fs > 3 = True
                            | otherwise = False
impliedOrs (Impc _ (Existsc _ (Disjc fs))) | length fs > 3 = True
                            | otherwise = False
impliedOrs (Forallc _ f) = impliedOrs f
impliedOrs (Existsc _ f) = impliedOrs f
impliedOrs (Conjc fs) = any impliedOrs fs
impliedOrs (Disjc fs) = any impliedOrs fs
impliedOrs (Impc _ f) = impliedOrs f
impliedOrs _ = False


{-
To make the visualisations, collect list of edges + characterstics
Edge = ((w_k, w_j), depth, ors, eq, neg, inClus, outClus) where
    (w_k, w_j) :  w_k sees w_j (generally through R, unless eq)
    depth : if depth is maximal for a subcluster, the edge is implied (dashed)
    ors : when ors != 0 represent implied disjunct by different colors (max 3)
    eq : when eq == True edge is equality between w_k and w_j (undirected edge)
    neg: when neg == True edge is impossible (red and filled)
    inClus, outClus : the clusters (in + out) are tuples (subclusID, 0/1/2) where
        0 represents not in conjunct or disjunct, 1 in conjunct, 2 in disjunct
        outClus : outer cluster to represent conjuncts/disjuncts of FOLforms
        inClus : inner cluster to represent possible conjuncts/disjuncts in the outer cluster FOLforms
-}
type Edge = ((String, String), Int, Int, Bool, Bool, Clust, Clust)
type Clust = (Int, Int, [Int], [Int])


toClusters :: FOLForm -> Int -> Int -> Bool -> Clust -> Clust -> [Edge]
toClusters Topc _ _ _ _ _ = undefined
toClusters (Pc _ _) _ _ _ _ _ = undefined
toClusters (Rc (VT (V k)) (VT (V j))) depth ors red clusIn clusOut = [(("x" ++ show k, "x" ++ show j), depth, ors, False, red, clusIn, clusOut)]
toClusters (Rc _ _) _ _ _ _ _  = undefined
toClusters (Eqdotc (VT (V k)) (VT (V j))) depth ors red clusIn clusOut = [(("x" ++ show j, "x" ++ show k), depth, ors, True, red, clusIn, clusOut)]
toClusters (Eqdotc _ _) _ _ _ _ _ = undefined
-- toClusters (Forallc vars (Impc f (Disjc gs))) depth ors red clusIn clus
toClusters (Forallc _ f) depth ors red clusIn clusOut = toClusters f depth ors red clusIn clusOut
toClusters (Existsc _ f) depth ors red clusIn clusOut = toClusters f depth ors red clusIn clusOut
toClusters (Conjc []) _ _ _ _ _ = []
toClusters (Conjc (f:fs)) depth ors red clusIn clusOut = toClusters f depth ors red clusIn clusOut ++ toClusters (Conjc fs) depth ors red clusIn clusOut
toClusters (Disjc []) _ _ _ _ _ = []
toClusters (Disjc (f:fs)) depth ors red clusIn clusOut | not (null (posForms (f:fs))) && not (null (negForms (f:fs))) = 
    toClusters (simpFOL1 (Impc (Conjc (negForms (f:fs))) (Disjc (posForms (f:fs))))) depth ors red clusIn clusOut
            |otherwise = toClusters f depth (ors + 1) red clusIn clusOut ++ toClusters (Disjc fs) depth (ors + 1) red clusIn clusOut
toClusters (Impc f g) depth ors red clusIn clusOut = toClusters f depth ors red clusIn clusOut ++ toClusters g (depth + 1) ors red clusIn clusOut
toClusters (Negc (Conjc fs)) depth ors red clusIn clusOut = concat [toClusters fi depth ors red clusIn clusOut | fi <- init fs] 
    ++ toClusters (last fs) (depth +1) ors (xor red True) clusIn clusOut
toClusters (Negc (Existsc _ f)) depth ors red clusIn clusOut = toClusters (Negc f) depth ors red clusIn clusOut
toClusters (Negc f) depth ors red clusIn clusOut = toClusters f depth ors (xor red True) clusIn clusOut

-- helper: sets depth, ors, eq to default for every (sub)cluster
toClusters1 :: FOLForm -> Clust -> Clust -> [Edge]
toClusters1 f = toClusters f 0 0 False

-- inner clusters
toClusters2 :: FOLForm -> Int -> Int -> [Int] -> [Int] -> [Edge]
toClusters2 (Conjc fs) m k vs vs2 = concat [toClusters1 f (n, 1, [], []) (m, k, vs, vs2) | (f, n) <- zip fs [0..]]
toClusters2 (Disjc fs) m  k vs vs2 = concat [toClusters1 f (n, 2, [], []) (m, k, vs, vs2) | (f, n) <- zip fs [0..]]
toClusters2 (Existsc vars (Conjc fs)) m k vs vs2 | hasForAllImp fs = concat [toClusters1 f (n, 1, getInts vars, []) (m, k, vs, vs2) | (f, n) <- zip fs [0..]]
toClusters2 (Existsc vars (Disjc fs)) m k vs vs2 | hasForAllImp fs = concat [toClusters1 f (n, 2, getInts vars, []) (m, k, vs, vs2) | (f, n) <- zip fs [0..]]
toClusters2 (Forallc vars (Disjc fs)) m  k vs vs2 = concat [toClusters1 f (n, 2, [] ,getInts vars) (m, k, vs, vs2) | (f, n) <- zip fs [0..]]
toClusters2 (Forallc vars (Existsc vars2 (Conjc fs))) m k vs vs2 = concat [toClusters1 f (n, 1, getInts vars2 ,getInts vars) (m, k, vs, vs2) | (f, n) <- zip fs [0..]]
toClusters2 f m k vs vs2 = toClusters1 f (0, 0, [], []) (m, k, vs, vs2)

-- outer clusters
toClusters3 :: FOLForm -> [Edge]
toClusters3 (Conjc fs) = concat [toClusters2 f m 1 [] []| (f,m) <- zip fs [0..]]
toClusters3 (Disjc fs) = concat [toClusters2 f m 2 [] []| (f,m) <- zip fs [0..]]
toClusters3 (Existsc vars (Conjc fs)) | hasForAllImp fs = concat [toClusters2 f m 1 (getInts vars) []| (f,m) <- zip fs [0..]]
toClusters3 (Existsc vars (Disjc fs)) | hasForAllImp fs =  concat [toClusters2 f m 2 (getInts vars) []| (f,m) <- zip fs [0..]]
toClusters3 (Forallc vars (Disjc fs)) | hasForAllImp fs = concat [toClusters2 f m 2 [] (getInts vars)| (f,m) <- zip fs [0..]]
toClusters3 (Forallc vars (Existsc vars2 (Conjc fs))) = concat [toClusters2 f m 1 (getInts vars2) (getInts vars)| (f,m) <- zip fs [0..]]
toClusters3 f = toClusters2 f 0 0 [] []

-- ors : colors for implied disjuncts 
myColors :: [X11Color]
myColors = [Black, DarkGreen, DarkViolet, SandyBrown]

toGraph :: [Edge] -> DotGraph String
toGraph edges = digraph (Str "G") $ do
    graphAttrs [style solid]
    -- first generate outer cluster(s)
    mapM_ (\ ((outClustInt, nao, outVars, outVars2), outClustName) -> do
        (if nao == 1 then 
                    (if null outVars && null outVars2 then 
                        do graphAttrs [textLabel "Conjunction (∧)", color Black]
                    else (if null outVars2 then 
                            do graphAttrs [toLabel ("∃ " ++ concatMap (\ var -> "x" ++ show var ++ " ") outVars ++ 
                                "s.t. Conjunction (∧)"::String), color Black]
                        else (if null outVars then 
                                do graphAttrs [toLabel ("∀ " ++ concatMap (\ var -> "x" ++ show var ++ " ") outVars2 ++ 
                                    "Conjunction (∧)"::String), color Black]
                            else graphAttrs [toLabel ("∀ " ++ concatMap (\ var -> "x" ++ show var ++ " ") outVars2 ++ 
                                ("∃ " ++ concatMap (\ var -> "x" ++ show var ++ " ") outVars ++ 
                                "s.t. Conjunction (∧)"::String)), color Black]
                            )
                        )
                    )
                else (if nao == 2 then
                        (if null outVars && null outVars2 then 
                            do graphAttrs [textLabel "Disjunction (∨)", color Black]
                        else (if null outVars2 then 
                                do graphAttrs [toLabel ("∃ " ++ concatMap (\ var -> "x" ++ show var ++ " ") outVars ++ 
                                    "s.t. Disjunction (∨)"::String), color Black]
                            else (if null outVars then 
                                    do graphAttrs [toLabel ("∀ " ++ concatMap (\ var -> "x" ++ show var ++ " ") outVars2 ++ 
                                        "Disjunction (∨)"::String), color Black]
                                else graphAttrs [toLabel ("∀ " ++ concatMap (\ var -> "x" ++ show var ++ " ") outVars2 ++
                                     ("∃ " ++ concatMap (\ var -> "x" ++ show var ++ " ") outVars ++ 
                                     "s.t. Disjunction (∨)"::String)), color Black]
                                )   
                            )
                        )
                    else graphAttrs [textLabel "", color White]
                    )
                    )
        cluster outClustName $ do
            -- generate inner cluster(s)
            mapM_ (\ ((inClustInt, naoIn, inVars, inVars2), inClustName) -> do
                (if naoIn == 1 then 
                    (if null inVars && null inVars2 then 
                        do graphAttrs [textLabel "Conjunction (∧)", color Black]
                    else (if null inVars2 then 
                            do graphAttrs [toLabel ("∃ " ++ concatMap (\ var -> "x" ++ show var ++ " ") inVars ++ 
                                "s.t. Conjunction (∧)"::String), color Black]
                        else (if null inVars then 
                                do graphAttrs [toLabel ("∀ " ++ concatMap (\ var -> "x" ++ show var ++ " ") inVars2 ++ 
                                    "Conjunction (∧)"::String), color Black]
                            else graphAttrs [toLabel ("∀ " ++ concatMap (\ var -> "x" ++ show var ++ " ") inVars2 ++ 
                                ("∃ " ++ concatMap (\ var -> "x" ++ show var ++ " ") inVars ++ 
                                "s.t. Conjunction (∧)"::String)), color Black]
                            )
                        )
                    )
                else (if naoIn == 2 then
                        (if null inVars && null inVars2 then 
                            do graphAttrs [textLabel "Disjunction (∨)", color Black]
                        else (if null inVars2 then 
                                do graphAttrs [toLabel ("∃ " ++ concatMap (\ var -> "x" ++ show var ++ " ") inVars ++ 
                                    "s.t. Disjunction (∨)"::String), color Black]
                            else (if null inVars then 
                                    do graphAttrs [toLabel ("∀ " ++ concatMap (\ var -> "x" ++ show var ++ " ") inVars2 ++ 
                                        "Disjunction (∨)"::String), color Black]
                                else graphAttrs [toLabel ("∀ " ++ concatMap (\ var -> "x" ++ show var ++ " ") inVars2 ++ 
                                    ("∃ " ++ concatMap (\ var -> "x" ++ show var ++ " ") inVars ++ 
                                    "s.t. Disjunction (∨)"::String)), color Black]
                                )   
                            )
                        )
                    else graphAttrs [textLabel "", color White]
                    )
                    )
               
               -- outline around clusters
                cluster inClustName $ do
                    (if nao /= 0 || naoIn /= 0 then do
                        graphAttrs [textLabel "", color Black]
                    else graphAttrs [textLabel "", color White])

                    -- make visualization of each of the inner clusters
                    mapM_ (\ ((s1,s2), depth, ors, eq, red, clusIn, clusOut) -> do
                        let maxDep = maximum [d | (_,d,_,_,_,_,_) <- 
                                filter (curClusOr1 (inClustInt, naoIn, inVars, inVars2) (outClustInt, nao, outVars, outVars2) ors) edges]
                        let n1 = s1 ++ show clusIn ++ show clusOut
                        let n2 = s2 ++ show clusIn ++ show clusOut

                        -- locality of corr. + implied worlds
                        node n1 [color $ 
                                    if s1 `elem` asWorlds (inVars ++ outVars) then do DarkOliveGreen
                                    else (if s1 `elem` asWorlds (inVars2 ++ outVars2) then do Blue
                                        else Black),

                            if s1 == "x0" then do textLabel "x" else toLabel (s1::String),
                            shape $ if s1 == "x0" then do DoubleCircle else Circle]
                        node n2 [color $ 
                                    if s2 `elem` asWorlds (inVars ++ outVars) then do DarkOliveGreen
                                    else (if s2 `elem` asWorlds (inVars2 ++ outVars2) then do Blue
                                        else Black),

                            if s2 == "x0" then do textLabel "x" else toLabel (s2::String),
                            shape $ if s2 == "x0" then do DoubleCircle else Circle]

                        edgeAttrs [ style $ if depth == maxDep then dashed else solid
                                , color $ if red then Red else myColors!!ors
                                , edgeEnds Forward
                                , textLabel $ if red then " × " else ""
                                , arrowTo $ if red then box else normal]
                        if eq then do
                            edgeAttrs [style dotted, color (myColors!!ors), edgeEnds NoDir, textLabel "  = "]
                            n1 --> n2
                        else do
                            n1 --> n2

                        ) (filter (curClus1 (inClustInt, naoIn, inVars, inVars2) (outClustInt, nao, outVars, outVars2)) edges)
                ) (zipGrIDs (getInClustersProvOut edges (outClustInt, nao, outVars, outVars2)) (getInClustersProvOut edges (outClustInt, nao, outVars, outVars2)))
        ) (zipGrIDs (getOutClusters edges) (getOutClusters edges))

asWorlds :: [Int] -> [String]
asWorlds = map (\ k -> "x" ++ show k)

-- helper to get maxDepth (implied/dashed)
curClusOr1 :: Clust -> Clust -> Int -> Edge -> Bool
curClusOr1 (cIn, cInTp, _, _) (cOut, cOutTp, _, _)  orCur (_,_,or1,_,_,(c1, c1Tp, _, _),(c2, c2Tp, _, _)) | orCur == 0 && cIn == c1 && cOut == c2
                                        && cInTp == c1Tp && cOutTp == c2Tp = True
                                        | cIn == c1 && cOut == c2 && cInTp == c1Tp && cOutTp == c2Tp && orCur == or1 = True
                                        | otherwise = False
                                   
-- is outer+inner subcluster
curClus1 :: Clust -> Clust -> Edge -> Bool
curClus1 cIn cOut (_,_,_,_,_,c1,c2) | cIn == c1 && cOut == c2 = True
                                    | otherwise = False

-- get the inner subcluster provided outer cluster
getInClustersProvOut :: [Edge] -> Clust -> [Clust]
getInClustersProvOut [] _ = []
getInClustersProvOut ((_,_,_,_,_,c1,c2):rest) cOut | c2 == cOut = nub (c1 : getInClustersProvOut rest cOut)
                                                    | otherwise = getInClustersProvOut rest cOut
getOutClusters :: [Edge] -> [Clust]
getOutClusters [] = []
getOutClusters ((_,_,_,_,_,_,c):rest) = nub (c : getOutClusters rest)

-- get cluster tuples + cluster IDs
zipGrIDs :: [Clust] -> [Clust] -> [(Clust, GraphID)]
zipGrIDs [] _ = []
zipGrIDs _ [] = []
zipGrIDs (i:rest) ((j1,j2,_,_):rest2) = (i,toGraphID (j1 * 10 + j2)) : zipGrIDs rest rest2


-- special cases : Top + Bot
topViz :: DotGraph String
topViz = digraph (Str "G") $ do
        graphAttrs [style solid, color White]
        node "x" [shape DoubleCircle, color Black]

botViz :: DotGraph String
botViz = digraph (Str "G") $ do
        graphAttrs [style solid, color White]
        node "x" [shape DoubleCircle, color Red]
