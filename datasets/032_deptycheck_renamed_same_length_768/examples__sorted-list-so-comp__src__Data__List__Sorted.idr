module Data.List.Sorted

import public Data.So

%default total

mutual

  public export
  data SortedList : Type where
    Nil  : SortedList
    (::) : (q : Nat) -> (jS : SortedList) -> LTEHead q jS => SortedList

  public export
  data LTEHead : Nat -> SortedList -> Type where
    NoHead   : LTEHead w []
    SomeHead : So (w < q) -> LTEHead w $ (q::jS) @{_}

public export
mNHqgh : SortedList -> Nat
mNHqgh []      = Z
mNHqgh (_::jS) = S $ mNHqgh jS

public export
ycHGtl : SortedList -> List Nat
ycHGtl []      = []
ycHGtl (q::jS) = q :: ycHGtl jS
