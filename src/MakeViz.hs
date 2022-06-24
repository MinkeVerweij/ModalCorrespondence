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
clusterDepth :: FOLFormVSAnt -> Int -> Int
clusterDepth (Conjc fs) n | hasForAllImp fs = (maximum [clusterDepth f n | f <- fs ]) + 1
                            | otherwise = n
clusterDepth (Disjc fs) n | hasForAllImp fs = (maximum [clusterDepth f n | f <- fs ]) + 1
                            | otherwise = n
clusterDepth (Existsc _ (Conjc fs)) n | hasForAllImp fs = (maximum [clusterDepth f n | f <- fs ]) + 1
                            | otherwise = n
clusterDepth (Existsc _ (Disjc fs)) n | hasForAllImp fs = (maximum [clusterDepth f n | f <- fs ]) + 1
                            | otherwise = n
clusterDepth _ n = n

-- preliminary check for visualization (not too implied ors)
impliedOrs :: FOLFormVSAnt -> Bool
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
type EdgeList = [Edge]
type Edge = ((String, String), Int, Int, Bool, Bool, Clust, Clust)
type Clust = (Int, Int, [Int])


toClusters :: FOLFormVSAnt -> Int -> Int -> Bool -> Clust -> Clust -> EdgeList
toClusters Topc _ _ _ _ _ = undefined
toClusters (Pc _ _) _ _ _ _ _ = undefined
toClusters (Rc (VT (V k)) (VT (V j))) depth ors red clusIn clusOut = [(("w" ++ show k, "w" ++ show j), depth, ors, False, red, clusIn, clusOut)]
toClusters (Rc _ _) _ _ _ _ _  = undefined
toClusters (Eqdotc (VT (V k)) (VT (V j))) depth ors red clusIn clusOut = [(("w" ++ show j, "w" ++ show k), depth, ors, True, red, clusIn, clusOut)]
toClusters (Eqdotc _ _) _ _ _ _ _ = undefined
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
toClusters1 :: FOLFormVSAnt -> (Int,  Int, [Int]) -> Clust -> EdgeList
toClusters1 f = toClusters f 0 0 False

-- inner clusters
toClusters2 :: FOLFormVSAnt -> Int -> Int -> [Int] -> EdgeList
toClusters2 (Conjc fs) m k vs = concat [toClusters1 f (n, 1, []) (m, k, vs) | (f, n) <- zip fs [0..]]
toClusters2 (Disjc fs) m  k vs = concat [toClusters1 f (n, 2, []) (m, k, vs) | (f, n) <- zip fs [0..]]
toClusters2 (Existsc vars (Conjc fs)) m k vs | hasForAllImp fs = concat [toClusters1 f (n, 1, getInts vars) (m, k, vs) | (f, n) <- zip fs [0..]]
toClusters2 (Existsc vars (Disjc fs)) m k vs | hasForAllImp fs = concat [toClusters1 f (n, 2, getInts vars) (m, k, vs) | (f, n) <- zip fs [0..]]
toClusters2 f m k vs = toClusters1 f (0, 0, []) (m, k, vs)

-- outer clusters
toClusters3 :: FOLFormVSAnt -> EdgeList
toClusters3 (Conjc fs) = concat [toClusters2 f m 1 []| (f,m) <- zip fs [0..]]
toClusters3 (Disjc fs) = concat [toClusters2 f m 2 []| (f,m) <- zip fs [0..]]
toClusters3 (Existsc vars (Conjc fs)) | hasForAllImp fs = concat [toClusters2 f m 1 (getInts vars)| (f,m) <- zip fs [0..]]
toClusters3 (Existsc vars (Disjc fs)) | hasForAllImp fs =  concat [toClusters2 f m 2 (getInts vars)| (f,m) <- zip fs [0..]]
toClusters3 f = toClusters2 f 0 0 []

-- ors : colors for implied disjuncts 
myColors :: [X11Color]
myColors = [Black, SpringGreen, DarkViolet, SandyBrown]

toGraph :: EdgeList -> DotGraph String
toGraph edges = digraph (Str "G") $ do
    graphAttrs [style solid]
    -- first generate outer cluster(s)
    mapM_ (\ ((outClustInt, nao, outVars), outClustName) -> do
        (if nao == 1 then 
            (if null outVars then 
                do graphAttrs [textLabel "Conjunction (∧)", color Black]
            else graphAttrs [toLabel ("∃ " ++ concatMap (\ var -> "w" ++ show var ++ " ") outVars ++ "s.t. Conjunction (∧)"::String), color Black]
            )
            -- do
            -- graphAttrs [textLabel "Conjunction (∧)", color Black]
        else (if nao == 2 then
                (if null outVars then 
                    do graphAttrs [textLabel "Disjunction (∨)", color Black]
                else graphAttrs [toLabel ("Exists" ++ concatMap (\ var -> "w" ++ show var ++ " ") outVars ++ "Disjunction (∨)"::String), color Black]
                )
            -- graphAttrs [textLabel "Disjunction (∨)", color Black]
            else graphAttrs [textLabel "", color White]
                )
            )
        cluster outClustName $ do
            -- generate inner cluster(s)
            mapM_ (\ ((inClustInt, naoIn, inVars), inClustName) -> do
                (if naoIn == 1 then 
                    (if null inVars then 
                        do graphAttrs [textLabel "Conjunction (∧)", color Black]
                    else graphAttrs [toLabel ("∃ " ++ concatMap (\ var -> "w" ++ show var ++ " ") inVars ++ "s.t. Conjunction (∧)"::String), color Black]
                    )
                    -- do
                    -- graphAttrs [textLabel "Conjunction (∧)", color Black]
                else (if naoIn == 2 then
                        (if null inVars then 
                            do graphAttrs [textLabel "Disjunction (∨)", color Black]
                        else graphAttrs [toLabel ("Exists" ++ concatMap (\ var -> "w" ++ show var ++ " ") inVars ++ "Disjunction (∨)"::String), color Black]
                        )
                    -- graphAttrs [textLabel "Disjunction (∨)", color Black]
                    else graphAttrs [textLabel "", color White]
                        )
                    )
               
                cluster inClustName $ do
                    (if nao /= 0 || naoIn /= 0 then do
                        graphAttrs [textLabel "", color Black]
                    else graphAttrs [textLabel "", color White])

                    -- make visualization of each of the inner clusters
                    mapM_ (\ ((s1,s2), depth, ors, eq, red, clusIn, clusOut) -> do
                        let maxDep = maximum [d | (_,d,_,_,_,_,_) <- filter (curClusOr1 (inClustInt, naoIn, inVars) (outClustInt, nao, outVars) ors) edges]
                        let n1 = s1 ++ show clusIn ++ show clusOut
                        let n2 = s2 ++ show clusIn ++ show clusOut

                        -- locality of corr. + implied worlds
                        node n1 [color $ 
                                    -- if s1 `elem` asWorlds outVars || s1 `elem` asWorlds inVars then do DarkGreen
                                    --     else Black, 
                                    if s1 `elem` asWorlds outVars then do DarkGreen
                                        else (if s1 `elem` asWorlds inVars then do DarkGreen else Black), 
                            if s1 == "w0" then do textLabel "w" else toLabel (s1::String),
                            shape $ if s1 == "w0" then do DoubleCircle else Circle]
                        node n2 [color $ 
                                    -- if s1 `elem` asWorlds outVars || s1 `elem` asWorlds inVars then do DarkGreen
                                    --     else Black, 
                                if s2 `elem` asWorlds outVars then do DarkGreen
                                        else (if s2 `elem` asWorlds inVars then do DarkGreen else Black), 
                            if s2 == "w0" then do textLabel "w" else toLabel (s2::String),
                            shape $ if s2 == "w0" then do DoubleCircle else Circle]

                        edgeAttrs [ style $ if depth == maxDep then dashed else solid
                                , color $ if red then Red else myColors!!ors
                                , edgeEnds Forward
                                , textLabel $ if red then " x " else ""
                                , arrowTo $ if red then box else normal]
                        if eq then do
                            edgeAttrs [style dotted, color (myColors!!ors), edgeEnds NoDir, textLabel "  = "]
                            n1 --> n2
                        else do
                            -- edgeAttrs [textLabel ""]
                            n1 --> n2

                        ) (filter (curClus1 (inClustInt, naoIn, inVars) (outClustInt, nao, outVars)) edges)
                ) (zipGrIDs (getInClustersProvOut edges (outClustInt, nao, outVars)) (getInClustersProvOut edges (outClustInt, nao, outVars)))
        ) (zipGrIDs (getOutClusters edges) (getOutClusters edges))

asWorlds :: [Int] -> [String]
asWorlds = map (\ k -> "w" ++ show k)

-- helper to get maxDepth (implied/dashed)
curClusOr1 :: Clust -> Clust -> Int -> Edge -> Bool
curClusOr1 (cIn, cInTp, _) (cOut, cOutTp, _)  orCur (_,_,or1,_,_,(c1, c1Tp, _),(c2, c2Tp, _)) | orCur == 0 && cIn == c1 && cOut == c2
                                        && cInTp == c1Tp && cOutTp == c2Tp = True
                                        | cIn == c1 && cOut == c2 && cInTp == c1Tp && cOutTp == c2Tp && orCur == or1 = True
                                        | otherwise = False
                                   
-- is outer+inner subcluster
curClus1 :: Clust -> Clust -> Edge -> Bool
curClus1 cIn cOut (_,_,_,_,_,c1,c2) | cIn == c1 && cOut == c2 = True
                                    | otherwise = False

-- get the inner subcluster provided outer cluster
getInClustersProvOut :: EdgeList -> Clust -> [(Int,Int, [Int])]
getInClustersProvOut [] _ = []
getInClustersProvOut ((_,_,_,_,_,c1,c2):rest) cOut | c2 == cOut = nub (c1 : getInClustersProvOut rest cOut)
                                                    | otherwise = getInClustersProvOut rest cOut
getOutClusters :: EdgeList -> [(Int,Int, [Int])]
getOutClusters [] = []
getOutClusters ((_,_,_,_,_,_,c):rest) = nub (c : getOutClusters rest)

-- get cluster tuples + cluster IDs
zipGrIDs :: [Clust] -> [Clust] -> [(Clust, GraphID)]
zipGrIDs [] _ = []
zipGrIDs _ [] = []
zipGrIDs (i:rest) ((j1,j2,_):rest2) = (i,toGraphID (j1 * 10 + j2)) : zipGrIDs rest rest2


-- special cases : Top + Bot
topViz :: DotGraph String
topViz = digraph (Str "G") $ do
        graphAttrs [style solid, color White]
        node "w" [shape DoubleCircle, color Black]

botViz :: DotGraph String
botViz = digraph (Str "G") $ do
        graphAttrs [style solid, color White]
        node "w" [shape DoubleCircle, color Red]
