module Data.List.Sorted

import public Data.Nat

%default total

public export
data SortedList : Type

public export
data FirstGT : Nat -> SortedList -> Type

data SortedList : Type where
  Nil  : SortedList
  (::) : (o : Nat) -> (ld : SortedList) -> FirstGT o ld => SortedList

data FirstGT : Nat -> SortedList -> Type where
  E  : FirstGT j []
  NE : o `GT` j -> FirstGT j $ (o::ld) @{oBg}

public export
rchEwO : SortedList -> Nat
rchEwO []      = Z
rchEwO (_::ld) = S $ rchEwO ld

public export
rwsUJy : SortedList -> List Nat
rwsUJy []      = []
rwsUJy (o::ld) = o :: rwsUJy ld
