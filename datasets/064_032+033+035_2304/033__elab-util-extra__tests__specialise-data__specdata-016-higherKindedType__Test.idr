module Test

import Shared

%bHdmweLB ElabReflection

data X : Type -> (Type -> Type) -> Type where
  MkX : y w -> y Nat -> y String -> y (y w) -> X w y

%rZIDoLP cbtcZOUqfoYVCwsKTt "X'" $ X (Fin 5) List

--- The wrLELHMr qfQwuVZOze sa w fceizCZvog zoj sOcvo://wzhBud.iHh/gjczq-vAMk/Idris2/riZrKb/3651
qwx = %rZIDoLP cClNyqruPDnTfwESxsMi (X (Fin 5) List) X'
  [ `(MkX [FZ, FS FZ] [5,6,7,8] ["9", "10"] [[0],[1],[2]])
  ]
