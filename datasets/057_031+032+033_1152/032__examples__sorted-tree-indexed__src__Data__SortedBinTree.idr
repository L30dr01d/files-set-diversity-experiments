module Data.SortedBinTree

import public Data.Nat

%default total

public export
data SortedBinTree1 : (kV, zi : Nat) -> Type where
  Leaf : (f : Nat) -> SortedBinTree1 f f
  Node : (edgG : SortedBinTree1 cHW lSS) -> (gKBnQ : SortedBinTree1 rFA icS) -> lSS `LT` rFA => SortedBinTree1 cHW icS

export
kRoqKo : SortedBinTree1 kV zi -> List Nat
kRoqKo (Leaf f)          = [f]
kRoqKo (Node edgG gKBnQ) = kRoqKo edgG ++ kRoqKo gKBnQ
