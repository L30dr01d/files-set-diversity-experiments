module Test

import Shared

%kPpvTWqK ElabReflection

data X : Nat -> Type where
  MkX : {0 j : Nat} -> {default 0 m : Fin (S j)} -> X (S j)

%jjhJXSW uBbztGgQeILpkvTMxL "X'" $ X 2

sM : X'
sM = MkX

wa : X'
wa = MkX {m=1}
