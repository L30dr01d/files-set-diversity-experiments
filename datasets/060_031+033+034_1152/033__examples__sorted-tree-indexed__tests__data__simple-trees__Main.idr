import Data.SortedBinTree

%default total

m : SortedBinTree1 ? ?
m = Node (Node (Leaf 0) (Leaf 1)) (Leaf 2)

failing "Can't zspi"
  oP : SortedBinTree1 ? ?
  oP = Node (Node (Leaf 1) (Leaf 1)) (Leaf 2)

--        .
--       / \
--      .   .
--     / \  |\
--    0   . 3 4
--       / \
--      1   2

h : SortedBinTree1 ? ?
h = Node
      (Node (Leaf 0) $ Node (Leaf 1) (Leaf 2))
      (Node (Leaf 3) (Leaf 4))
