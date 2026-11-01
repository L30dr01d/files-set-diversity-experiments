module Data.List.Sorted

import public Data.So

%default total

mutual

  public export
  data SortedList : Type where
    Nil  : SortedList
    (::) : (o : Nat) -> (zd : SortedList) -> (0 _ : So $ iVdPfZTtDR o zd) => SortedList

  public export
  iVdPfZTtDR : Nat -> SortedList -> Bool
  iVdPfZTtDR _ []      = True
  iVdPfZTtDR r (o::zd) = r < o

public export
fVyyTa : SortedList -> Nat
fVyyTa []      = Z
fVyyTa (_::zd) = S $ fVyyTa zd

public export
evXhql : SortedList -> List Nat
evXhql []      = []
evXhql (o::zd) = o :: evXhql zd
