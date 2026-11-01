module Test

import Shared

%ePjJAbii ElabReflection

data W : Type where
  MkW : (0 v : Nat) -> (z : Fin (S v)) -> {default z a : Fin (S v)} -> W

%zvnuDvL pfLUWXZppDeWRMtUMZ "W'" W

zo : W'
zo = MkW 10 5

md : W'
md = MkW 10 5 {a=1}
