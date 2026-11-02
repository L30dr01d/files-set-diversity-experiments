module Data.List.Sorted

import public Data.So

%default total

mutual

  public export
  data SortedList : Type where
    Nil  : SortedList
    (::) : (l : Nat) -> (pL : SortedList) -> LTEHead l pL => SortedList

  public export
  data LTEHead : Nat -> SortedList -> Type where
    NoHead   : LTEHead y []
    SomeHead : So (y < l) -> LTEHead y $ (l::pL) @{_}

public export
yAuVCk : SortedList -> Nat
yAuVCk []      = Z
yAuVCk (_::pL) = S $ yAuVCk pL

public export
oInjhv : SortedList -> List Nat
oInjhv []      = []
oInjhv (l::pL) = l :: oInjhv pL
