{-#LANGUAGE OverloadedStrings#-}
module MakeViz where
import Data.GraphViz.Types.Monadic
import Data.GraphViz.Attributes
import Data.GraphViz.Types.Generalised
import Languages
import Data.Bits
import Data.List
import Data.GraphViz (ToGraphID(toGraphID))

-- ((p-><>p)&(<>p->p))|((q-><><>q)&(<>q-><><>q))
-- ((p-><>p)|(q-><><>q))&((<>p->p)|(<>q-><><>q))

type EdgeList = [Edge]
type Edge = ((String, String), Int, Int, Bool, Bool, (Int, Int), (Int, Int))
-- (Forallc [V 3] (Negc (Existsc [V 1,V 2] (Conjc [Rc (VT (V 0)) (VT (V 1)),Rc (VT (V 1)) (VT (V 2)),Rc (VT (V 2)) (VT (V 3))]))))
-- (Existsc [V 1] (Conjc [Rc (VT (V 0)) (VT (V 1)),Forallc [V 2] (Negc (Rc (VT (V 1)) (VT (V 2))))]))

-- each elem in output ((from, to), D (int), O (int), Eq (Bool), Neg (Bool), outer (int)) list represents edge
-- when D (depth) is maximal : edge is dotted (new cluster)
-- when O (ors) not 0: Or case distintion, edge different colors (new cluster for every diff O value)
-- when Eq (equality) True: add 2 edges, equality 'node' in between, edges undirected, 'nodes' filled (no line around =)
-- when Neg (not possible): edges are red and filled
-- when outer (is disj. or conj.) : make a new cluster with edge around it
toClusters :: FOLFormVSAnt -> Int -> Int -> Bool -> (Int, Int) -> (Int, Int) -> EdgeList -- (w_i,w_j), dotted/filled, color (or), eq (noDir), color (neg)
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
toClusters (Disjc (f:fs)) depth ors red clusIn clusOut = toClusters f depth (ors + 1) red clusIn clusOut ++ toClusters (Disjc fs) depth (ors + 1) red clusIn clusOut
toClusters (Impc f g) depth ors red clusIn clusOut = toClusters f depth ors red clusIn clusOut ++ toClusters g (depth + 1) ors red clusIn clusOut
toClusters (Negc (Conjc fs)) depth ors red clusIn clusOut = concat [toClusters fi depth ors red clusIn clusOut | fi <- init fs] 
    ++ toClusters (last fs) (depth +1) ors (xor red True) clusIn clusOut
toClusters (Negc (Existsc _ f)) depth ors red clusIn clusOut = toClusters (Negc f) depth ors red clusIn clusOut
toClusters (Negc f) depth ors red clusIn clusOut = toClusters f depth ors (xor red True) clusIn clusOut

-- toClusters :: FOLFormVSAnt -> Int -> Int -> Bool -> EdgeList -- (w_i,w_j), dotted/filled, color (or), eq (noDir), color (neg)
-- toClusters Topc _ _ _ = undefined
-- toClusters (Pc _ _) _ _ _ = undefined
-- toClusters (Rc (VT (V k)) (VT (V j))) depth ors red = [(("w" ++ show k, "w" ++ show j), depth, ors, False, red)]
-- toClusters (Rc _ _) _ _ _ = undefined
-- toClusters (Eqdotc (VT (V k)) (VT (V j))) depth ors red = [(("w" ++ show j, "w" ++ show k), depth, ors, True, red)]
-- toClusters (Eqdotc _ _) _ _ _ = undefined
-- toClusters (Forallc _ f) depth ors red = toClusters f depth ors red
-- toClusters (Existsc _ f) depth ors red = toClusters f depth ors red
-- toClusters (Conjc []) _ _ _ = []
-- toClusters (Conjc (f:fs)) depth ors red = toClusters f depth ors red ++ toClusters (Conjc fs) depth ors red
-- toClusters (Disjc []) _ _ _ = []
-- toClusters (Disjc (f:fs)) depth ors red = toClusters f depth (ors + 1) red ++ toClusters (Conjc fs) depth (ors + 2) red
-- toClusters (Impc f g) depth ors red = toClusters f depth ors red ++ toClusters g (depth + 1) ors red
-- toClusters (Negc (Conjc fs)) depth ors red = concat [toClusters fi depth ors red | fi <- init fs] 
--     ++ toClusters (last fs) (depth +1) ors (xor red True)
-- toClusters (Negc (Existsc _ f)) depth ors red = toClusters (Negc f) depth ors red
-- toClusters (Negc f) depth ors red = toClusters f depth ors (xor red True)

-- flattenClus :: [[(([Char], [Char]), Int, Int, Bool, Bool)]] -> [(([Char], [Char]), Int, Int, Bool, Bool)]
-- flattenClus = foldr (++) []
-- -- flattenClus [] = []
-- -- flattenClus (x:xs) = x ++ flattenClus xs

toClusters1 :: FOLFormVSAnt -> (Int,  Int) -> (Int, Int) -> EdgeList
toClusters1 f = toClusters f 0 0 False

toClusters2 :: FOLFormVSAnt -> Int -> Int -> EdgeList
toClusters2 (Conjc fs) m k = concat [toClusters1 f (n, 1) (m, k) | (f, n) <- zip fs [0..]]
toClusters2 (Disjc fs) m  k = concat [toClusters1 f (n, 2) (m, k) | (f, n) <- zip fs [0..]]
toClusters2 f m k = toClusters1 f (0, 0) (m, k)

toClusters3 :: FOLFormVSAnt -> EdgeList
toClusters3 (Conjc fs) = concat [toClusters2 f m 1| (f,m) <- zip fs [0..]]
toClusters3 (Disjc fs) = concat [toClusters2 f m 2| (f,m) <- zip fs [0..]]
toClusters3 f = toClusters2 f 0 0

-- toClusters2 :: FOLFormVSAnt -> EdgeList
-- toClusters2 (Conjc fs) = concat [toClusters3 f n| (f, n) <- zip fs [0..]]
-- toClusters2 (Disjc fs) = concat [toClusters3 f n| (f, n) <- zip fs [0..]]
-- toClusters2 f = toClusters1 f 0

-- toClusters3 :: FOLFormVSAnt -> Int -> EdgeList
-- toClusters3 (Conjc fs) = concat [toClusters1 f n| (f, n) <- zip fs [0..]]
-- toClusters3 (Disjc fs) = concat [toClusters1 f n| (f, n) <- zip fs [0..]]
-- toClusters3 f = toClusters1 f 0

-- myEdges :: EdgeList
-- myEdges = [(("w0","w0"),0,0,False,False,(0,0),(0,1)),(("w0","w2"),0,0,False,False,(0,0),(1,1)),(("w0","w2"),1,0,True,False,(0,0),(1,1))]

myColors :: [X11Color]
myColors = [Black, SpringGreen, DarkViolet, SandyBrown]

toGraph :: EdgeList -> DotGraph String
toGraph edges = digraph (Str "G") $ do
    nodeAttrs [shape Circle]
    graphAttrs [style solid]
    mapM_ (\ ((outClustInt, nao), outClustName) -> do
        (if nao == 1 then do
            graphAttrs [textLabel "Conjunction (∧)", color Black]
        else (if nao == 2 then do
            graphAttrs [textLabel "Disjunction (∨)", color Black]
            else graphAttrs [textLabel "", color White]
                )
            )
        cluster outClustName $ do
            mapM_ (\ ((inClustInt, naoIn), inClustName) -> do
                (if naoIn == 1 then do
                        graphAttrs [textLabel "Conjunction (∧)", color Black]
                    else (if naoIn == 2 then do
                            graphAttrs [textLabel "Disjunction (∨)", color Black]
                        else graphAttrs [textLabel "", color White]
                            )
                        )
               
                cluster inClustName $ do
                    (if nao /= 0 || naoIn /= 0 then do
                        graphAttrs [textLabel "", color Black]
                    else graphAttrs [textLabel "", color White])
                
                    mapM_ (\ ((s1,s2), depth, ors, eq, red, clusIn, clusOut) -> do
                        let maxDep = maximum [d | (_,d,_,_,_,_,_) <- filter (curClusOr1 (inClustInt, naoIn) (outClustInt, nao) ors) edges]
                        let n1 = s1 ++ show clusIn ++ show clusOut
                        let n2 = s2 ++ show clusIn ++ show clusOut

                        node n1 [color Black, toLabel (s1::String)]
                        node n2 [color Black, toLabel (s2::String)]
                        edgeAttrs [ style $ if depth == maxDep && not red then dashed else solid
                                , color $ if red then Red else myColors!!ors
                                , edgeEnds Forward]
                        if eq then do
                            edgeAttrs [style dotted, color (myColors!!ors), edgeEnds NoDir]
                            let eqNode = s1 ++ "=" ++ s2
                            node eqNode [color White, toLabel ("="::String)]
                            n1 --> eqNode
                            n2 --> eqNode
                        else
                            n1 --> n2

                        ) (filter (curClus1 (inClustInt, naoIn) (outClustInt, nao)) edges)
                ) (zipGrIDs (getInClustersProvOut edges (outClustInt, nao)) (getInClustersProvOut edges (outClustInt, nao)))
        ) (zipGrIDs (getOutClusters edges) (getOutClusters edges))

curClusOr1 :: (Int, Int) -> (Int, Int) -> Int -> Edge -> Bool
curClusOr1 cIn cOut orCur (_,_,or1,_,_,c1,c2) | orCur == 0 && cIn == c1 && cOut == c2 = True
                                        | cIn == c1 && cOut == c2 && orCur == or1 = True
                                        | otherwise = False

curClus1 :: (Int, Int) -> (Int, Int) -> Edge -> Bool
curClus1 cIn cOut (_,_,_,_,_,c1,c2) | cIn == c1 && cOut == c2 = True
                                    | otherwise = False

getInClustersProvOut :: EdgeList -> (Int, Int) -> [(Int,Int)]
getInClustersProvOut [] _ = []
getInClustersProvOut ((_,_,_,_,_,c1,c2):rest) cOut | c2 == cOut = nub (c1 : getInClustersProvOut rest cOut)
                                                    | otherwise = getInClustersProvOut rest cOut


getInClusters :: EdgeList -> [(Int,Int)]
getInClusters [] = []
getInClusters ((_,_,_,_,_,c,_):rest) = nub (c : getInClusters rest)

getOutClusters :: EdgeList -> [(Int,Int)]
getOutClusters [] = []
getOutClusters ((_,_,_,_,_,_,c):rest) = nub (c : getOutClusters rest)

zipGrIDs :: [(Int, Int)] -> [(Int, Int)] -> [((Int, Int), GraphID)]
zipGrIDs [] _ = []
zipGrIDs _ [] = []
-- zipGrIDs (i:rest) (j:rest2) = (i,toGraphID j) : zipGrIDs rest rest2
zipGrIDs (i:rest) ((j1,j2):rest2) = (i,toGraphID (j1 * 10 + j2)) : zipGrIDs rest rest2

-- curClusOr :: Int -> Int -> Edge -> Bool
-- -- curClus _ [] = []
-- curClusOr k orCur (_,_,or1,_,_,c)| orCur == 0 && k == c = True
--                         | k ==c && orCur == or1 = True -- (edge,a1,a2,a3,a4,c) : curClus k rest
--                         | otherwise = False        -- -- | otherwise = curClus k rest

-- curClus :: Int -> Edge -> Bool
-- -- curClus _ [] = []
-- curClus k (_,_,_,_,_,c)| k ==c = True -- (edge,a1,a2,a3,a4,c) : curClus k rest
--                         | otherwise = False 

-- getClusters :: EdgeList -> [Int]
-- getClusters [] = []
-- getClusters ((_,_,_,_,_,c):rest) = nub (c : getClusters rest)

-- toGraph :: EdgeList -> DotGraph String
-- toGraph edges = digraph (Str "G") $ do
--     -- let maxDepClus = maximum [ (d,c) | (_,d,_,_,_,c) <- edges ]
--     nodeAttrs [shape Circle]
--     graphAttrs [style solid, color Black]
    
--     mapM_ (\ (clust1, clust2) -> do
--         cluster clust2 $ do
--             graphAttrs [style solid, color Black]
--             mapM_ (\ ((s1,s2), depth, ors, eq, red, clus) -> do
--                 let maxDep = maximum [d | (_,d,_,_,_,_) <- filter (curClusOr clust1 ors) edges]
--                 let n1 = s1 ++ show clus
--                 let n2 = s2 ++ show clus

--                 node n1 [color Black, toLabel (s1::String)]
--                 node n2 [color Black, toLabel (s2::String)]
--                 edgeAttrs [ style $ if depth == maxDep && not red then dashed else solid
--                         , color $ if red then Red else myColors!!ors
--                         , edgeEnds Forward]
--                 if eq then do
--                     edgeAttrs [style dotted, color (myColors!!ors), edgeEnds NoDir]
--                     let eqNode = s1 ++ "=" ++ s2
--                     node eqNode [color White, toLabel ("="::String)]
--                     n1 --> eqNode
--                     n2 --> eqNode
--                     else
--                         n1 --> n2
--                 ) (filter (curClus clust1) edges)
--             ) (zip2 (getClusters edges) (getClusters edges))

-- zip2 :: [Int] -> [Int] -> [(Int, GraphID)]
-- zip2 [] _ = []
-- zip2 _ [] = []
-- zip2 (i:rest) (j:rest2) = (i,toGraphID j) : zip2 rest rest2
-- -- toGraph :: EdgeList -> DotGraph String
-- -- toGraph edges = digraph (Str "G") $ do
-- --     -- let maxDepClus = maximum [ (d,c) | (_,d,_,_,_,c) <- edges ]
-- --     nodeAttrs [shape Circle]
-- --     -- graphAttrs [style solid, color White]
    
-- --     mapM_ (\ ((s1,s2),depth,ors,eq,red, clus) -> do
-- --         let maxDep = maximum [ d | (_,d,_,_,_,_) <- filter (curClus clus) edges ]
-- --         let n1 = s1 ++ show clus
-- --         let n2 = s2 ++ show clus
-- --         -- let c = (Num clus)
-- --         -- -- cluster c graphAttrs [style solid, color Black]
-- --         -- cluster c $ do
-- --         --     graphAttrs [color Black]
-- --         graphAttrs [style solid, color Black]

-- --         node n1 [color Black, toLabel (s1::String)]
-- --         node n2 [color Black, toLabel (s2::String)]
-- --         edgeAttrs [ style $ if depth == maxDep && not red then dashed else solid
-- --                   , color $ if red then Red else myColors!!ors
-- --                   , edgeEnds Forward]
-- --         if eq then do
-- --             edgeAttrs [style dotted, color (myColors!!ors), edgeEnds NoDir]
-- --             let eqNode = s1 ++ "=" ++ s2
-- --             node eqNode [color White, toLabel ("="::String)]
-- --             n1 --> eqNode
-- --             n2 --> eqNode
-- --             else
-- --                 n1 --> n2
-- --         ) edges
    
-- -- (Existsc [V 1] (Conjc [Rc (VT (V 0)) (VT (V 1)),Forallc [V 2] (Negc (Rc (VT (V 1)) (VT (V 2))))]))
-- -- (Forallc [V 2] (Impc (Existsc [V 1] (Conjc [Rc (VT (V 0)) (VT (V 1)),Rc (VT (V 1)) (VT (V 2))])) (Rc (VT (V 2)) (VT (V 2)))))
-- -- (Forallc [V 3] (Negc (Existsc [V 1,V 2] (Conjc [Rc (VT (V 0)) (VT (V 1)),Rc (VT (V 1)) (VT (V 2)),Rc (VT (V 2)) (VT (V 3))]))))
-- -- (Existsc [V 1] (Conjc [Rc (VT (V 0)) (VT (V 1)),Forallc [V 2] (Negc (Rc (VT (V 1)) (VT (V 2))))]))