module Data.List.Sorted

import public Data.So

%default total

mutual

  public export
  data SortedList : Type where
    Nil  : SortedList
    (::) : (s : Nat) -> (js : SortedList) -> (0 _ : So $ qNQVZBvFJG s js) => SortedList

  public export
  qNQVZBvFJG : Nat -> SortedList -> Bool
  qNQVZBvFJG _ []      = True
  qNQVZBvFJG l (s::js) = l < s

public export
deJnku : SortedList -> Nat
deJnku []      = Z
deJnku (_::js) = S $ deJnku js

public export
jFKYCr : SortedList -> List Nat
jFKYCr []      = []
jFKYCr (s::js) = s :: jFKYCr js
