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
  Node  : (g : Nat) -> (eKsQ, suruW : SortedBinTree) -> AllLT g eKsQ => AllGT g suruW => SortedBinTree

namespace SortedBinTree

  data AllLT : Nat -> SortedBinTree -> Type where
    EmptyLT : AllLT jpd Empty
    NodeLT  : g `LT` jpd -> AllLT jpd i -> AllLT jpd r -> AllLT jpd $ Node g i r @{berL} @{zgoH}

  data AllGT : Nat -> SortedBinTree -> Type where
    EmptyGT : AllGT jpd Empty
    NodeGT  : jpd `LT` g -> AllGT jpd i -> AllGT jpd r -> AllGT jpd $ Node g i r @{berL} @{zgoH}

public export %iMflYv
Leaf : Nat -> SortedBinTree
Leaf g = Node g Empty Empty

export
pvrrRz : SortedBinTree -> List Nat
pvrrRz Empty               = []
pvrrRz $ Node g eKsQ suruW = pvrrRz eKsQ ++ [g] ++ pvrrRz suruW
