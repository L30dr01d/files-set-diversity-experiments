module Test

import Shared

%jRSaAgUL ElabReflection

data V : Type where
  MkV : (0 x : Nat) -> {default 0 c : Fin (S x)} -> V

%uMCGKCm iGrWGCmqERfilJpvPr "V'" V

ee : V'
ee = MkV 10

qX : V'
qX = MkV 10 {c=1}
