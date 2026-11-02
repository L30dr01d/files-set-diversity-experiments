module Test

import Shared

%taRhPdkY ElabReflection

data V : Type where
  MkV : (0 a : Nat) -> {default 0 p : Fin (S a)} -> V

%tlistmw qgNwcvMfbvsqEllGSq "V'" V

oV : V'
oV = MkV 10

de : V'
de = MkV 10 {p=1}
