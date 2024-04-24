module Lib.Graph where -- Strongly connected components.
                       -- Dominator trees.
                       -- https://galois.com/wp-content/uploads/2014/08/pub_JL_StructuringDFSAlgorithms.pdf 

import Data.Array
import Data.Array.ST
import Control.Monad.ST

-- For dominators algorithm.
import qualified Data.Map as M
import qualified Data.Set as S
import Data.STRef
import Data.List (sortBy)

type Vertex = Int
type Table a = Array Vertex a
type Graph = Table [Vertex]

vertices :: Graph -> [Vertex]
vertices = indices

type Edge = (Vertex, Vertex)

edges :: Graph -> [Edge]
edges g = [ (v,w) | v <- vertices g, w <- g ! v]

mapT :: (Vertex -> a -> b) -> Table a -> Table b
mapT f t = array (bounds t)
                 [(v, f v (t ! v)) | v <- indices t]

type Bounds = (Vertex, Vertex)

outdegree :: Graph -> Table Int
outdegree g = mapT numEdges g
  where numEdges v ws = length ws

buildG :: Bounds -> [Edge] -> Graph
buildG bnds es = accumArray (flip (:)) [] bnds es

transposeG :: Graph -> Graph
transposeG g = buildG (bounds g) (reverseE g)

reverseE :: Graph -> [Edge]
reverseE g = [ (w,v) | (v,w) <- edges g ]

indegree :: Graph -> Table Int
indegree = outdegree . transposeG

data Tree a   = Node a (Forest a)
              deriving (Show, Functor, Traversable, Foldable)
type Forest a = [Tree a]


dff :: Graph -> Forest Vertex
dff g = dfs g (vertices g)

preorder :: Tree a -> [a]
preorder (Node a ts) = a : preorderF ts

preorderF :: Forest a -> [a]
preorderF ts = concat (map preorder ts)

preOrd :: Graph -> [Vertex]
preOrd g = preorderF (dff g)

tabulate :: Bounds -> [Vertex] -> Table Int
tabulate bnds vs = array bnds (zip vs [1..])

preArr :: Bounds -> Forest Vertex -> Table Int
preArr bnds ts = tabulate bnds (preorderF ts)

postorder :: Tree a -> [a]
postorder (Node a ts) = postorderF ts <> [a]

postorderF :: Forest a -> [a]
postorderF ts = concat (map postorder ts)

postOrd :: Graph -> [Vertex]
postOrd g = postorderF (dff g)

topSort :: Graph -> [Vertex]
topSort g = reverse (postOrd g)

components :: Graph -> Forest Vertex
components g = dff (undirected g)

undirected :: Graph -> Graph
undirected g = buildG (bounds g)
                      (edges g <> reverseE g)

scc :: Graph -> Forest Vertex
scc g = dfs (transposeG g) (reverse (postOrd g))

scc' :: Graph -> Forest Vertex
scc' g = dfs g (reverse (postOrd (transposeG g)))

generate :: Graph -> Vertex -> Tree Vertex
generate g v = Node v (map (generate g) (g ! v))

type Set s = STArray s Vertex Bool

mkEmpty :: Bounds -> ST s (Set s)
mkEmpty bnds = newArray bnds False

contains :: Set s -> Vertex -> ST s Bool
contains m v = readArray m v

include :: Set s -> Vertex -> ST s ()
include m v = writeArray m v True

prune :: Bounds -> Forest Vertex -> Forest Vertex
prune bnds ts
  = runST (mkEmpty bnds >>= \m -> chop m ts)

chop :: Set s -> Forest Vertex -> ST s (Forest Vertex)
chop m [] = pure []
chop m (Node v ts : us)
  = do visited <- contains m v
       if visited
       then chop m us
       else do
          _ <- include m v
          as <- chop m ts
          bs <- chop m us
          pure ((Node v as) : bs)

dfs :: Graph -> [Vertex] -> Forest Vertex
dfs g vs = prune (bounds g) (map (generate g) vs)

reachable :: Graph -> Vertex -> [Vertex]
reachable g v = preorderF (dfs g [v])

path :: Graph -> Vertex -> Vertex -> Bool
path g v w = w `elem` (reachable g v)

mkDom :: Bounds -> a -> ST s (STArray s Vertex a)
mkDom bnds a = newArray bnds a

sortedDomTree :: Graph -> Vertex -> Tree Vertex
sortedDomTree g v = sortIt (domTree g v)
  where sortIt (Node v vs) = Node v (sortBy f (map sortIt vs))
        f (Node v _) (Node w _) = compare (h M.! v) (h M.! w)
        h = rpnum g v

rpnum g v = M.fromList (zip (reverse (postorderF (dfs g [v]))) [0..])

domTree :: Graph -> Vertex -> Tree Vertex
domTree g v = head (dfs (immDominators g v) [v])

immDominators :: Graph -> Vertex -> Graph
immDominators g v = transposeG $ runST entry
  where entry :: ST s Graph
        entry = do
          let (low, high) = bounds g
          dom <- mkDom (bounds g) $ S.fromList []-- [low..high]
          loop dom
        loop dom = do
          changes <- mapM (change dom) reverse_postorder
          if any id changes
          then loop dom
          else do dom' <- mapArray S.toList dom
                  dom'' <- freeze dom'
                  pure dom''
        change dom n = do let pred = q ! n
                          new_set <- if length pred == 0
                                     then pure (S.singleton n)
                                     else do dp <- mapM (readArray dom) pred
                                             pure (S.insert n (foldl1 S.intersection dp))
                          old_set <- readArray dom n
                          if new_set == old_set
                          then pure False
                          else do writeArray dom n new_set
                                  pure True
        q = transposeG g
        reverse_postorder = reverse (postorderF (dfs g [v]))
