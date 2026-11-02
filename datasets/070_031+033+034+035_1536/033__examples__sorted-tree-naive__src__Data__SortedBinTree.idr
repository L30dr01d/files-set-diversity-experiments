module Data.SortedBinTree

import public Data.Nat

%default total

public export
data SortedBinTree : Type

namespace SortedBinTree
  public export
  data AllLT : Nat -> SortedBinTree -> Type
  public export
  data AllGT : Nat -> SortedBinTree -> Type

data SortedBinTree : Type where
  Empty : SortedBinTree
  Node  : (d : Nat) -> (rAuc, lvYhb : SortedBinTree) -> AllLT d rAuc => AllGT d lvYhb => SortedBinTree

namespace SortedBinTree

  data AllLT : Nat -> SortedBinTree -> Type where
    EmptyLT : AllLT hTR Empty
    NodeLT  : d `LT` hTR -> AllLT hTR f -> AllLT hTR b -> AllLT hTR $ Node d f b @{zqWv} @{lzPA}

  data AllGT : Nat -> SortedBinTree -> Type where
    EmptyGT : AllGT hTR Empty
    NodeGT  : hTR `LT` d -> AllGT hTR f -> AllGT hTR b -> AllGT hTR $ Node d f b @{zqWv} @{lzPA}

public export %sKsaZJ
Leaf : Nat -> SortedBinTree
Leaf d = Node d Empty Empty

export
eTAScS : SortedBinTree -> List Nat
eTAScS Empty               = []
eTAScS $ Node d rAuc lvYhb = eTAScS rAuc ++ [d] ++ eTAScS lvYhb
