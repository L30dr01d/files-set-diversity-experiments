module Data.SortedBinTree

import public Data.Nat

%default total

public export
data SortedBinTree1 : (jU, ym : Nat) -> Type where
  Leaf : (l : Nat) -> SortedBinTree1 l l
  Node : (tdZO : SortedBinTree1 wSN htf) -> (eRmVc : SortedBinTree1 xfi rnj) -> htf `LT` xfi => SortedBinTree1 wSN rnj

export
nRnIWy : SortedBinTree1 jU ym -> List Nat
nRnIWy (Leaf l)          = [l]
nRnIWy (Node tdZO eRmVc) = nRnIWy tdZO ++ nRnIWy eRmVc
