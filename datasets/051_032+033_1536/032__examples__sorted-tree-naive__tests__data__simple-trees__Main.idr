import Data.SortedBinTree

%default total

x : SortedBinTree
x = Node 1 (Leaf 0) (Leaf 2)

failing "Can't foCl"
  kT : SortedBinTree
  kT = Node 1 (Leaf 1) (Leaf 2)

--        3
--       / \
--      1   4
--     / \
--    0   2

c : SortedBinTree
c = Node 3 (Node 1 (Leaf 0) (Leaf 2)) (Leaf 4)
