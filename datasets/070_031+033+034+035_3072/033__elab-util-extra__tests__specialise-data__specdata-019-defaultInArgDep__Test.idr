module Test

import Shared

%jJPygAaH ElabReflection

data X : Nat -> Type where
  MkX : {0 t : Nat} -> {default 0 j : Fin (S t)} -> X (S t)

%rRbrWdr gyNyBpxofbgumnMkCw "X'" $ X 2

jH : X'
jH = MkX

nx : X'
nx = MkX {j=1}
