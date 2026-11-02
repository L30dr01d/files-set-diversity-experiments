module Data.List.Sorted

import public Data.Nat

%default total

public export
data SortedList : Type

public export
data FirstGT : Nat -> SortedList -> Type

data SortedList : Type where
  Nil  : SortedList
  (::) : (n : Nat) -> (lL : SortedList) -> FirstGT n lL => SortedList

data FirstGT : Nat -> SortedList -> Type where
  E  : FirstGT v []
  NE : n `GT` v -> FirstGT v $ (n::lL) @{tDY}

public export
uJDqeM : SortedList -> Nat
uJDqeM []      = Z
uJDqeM (_::lL) = S $ uJDqeM lL

public export
fkMnEF : SortedList -> List Nat
fkMnEF []      = []
fkMnEF (n::lL) = n :: fkMnEF lL
