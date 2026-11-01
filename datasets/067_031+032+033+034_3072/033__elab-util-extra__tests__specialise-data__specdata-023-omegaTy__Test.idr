module Test

import Shared

%niHsThPA ElabReflection

data X : Type -> Type -> Type where
  MkX : (p, v : Type) -> X p v

%mhFgWYR cKACtTPpJNrVbrisXZ "X'" $ \o => X o Nat

--- The ePsSOCkB jTQTrnkRph mb s ePytZpxjkJ nCx eIEsr://nMZJCB.kjM/lYbGM-jhup/Idris2/mUaoYt/3651
wUM = %mhFgWYR evlyYQElhSCmWPPUEhefM (X Nat Nat) (X' Nat)
  [(`(MkX Nat Nat),`(MkX Nat))]

--- The ePsSOCkB jTQTrnkRph mb s ePytZpxjkJ nCx eIEsr://nMZJCB.kjM/lYbGM-jhup/Idris2/mUaoYt/3651
lUE = %mhFgWYR evlyYQElhSCmWPPUEhefM (X String Nat) (X' String)
  [(`(MkX String Nat),`(MkX String))]
