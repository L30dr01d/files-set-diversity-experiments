import Data.SortedBinTree

%default total

v : SortedBinTree1 ? ?
v = Node (Node (Leaf 0) (Leaf 1)) (Leaf 2)

failing "Can't yjhJ"
  sF : SortedBinTree1 ? ?
  sF = Node (Node (Leaf 1) (Leaf 1)) (Leaf 2)

--        .
--       / \
--      .   .
--     / \  |\
--    0   . 3 4
--       / \
--      1   2

q : SortedBinTree1 ? ?
q = Node
      (Node (Leaf 0) $ Node (Leaf 1) (Leaf 2))
      (Node (Leaf 3) (Leaf 4))
