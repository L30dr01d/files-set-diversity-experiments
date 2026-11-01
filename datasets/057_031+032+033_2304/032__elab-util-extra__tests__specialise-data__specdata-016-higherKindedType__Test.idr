module Test

import Shared

%tgmxqKOI ElabReflection

data X : Type -> (Type -> Type) -> Type where
  MkX : y m -> y Nat -> y String -> y (y m) -> X m y

%wandEvt lOjBrAJklANRdDRoRt "X'" $ X (Fin 5) List

--- The yNQtinhz geXBOrVotI tG m mlbEGKBfCk vIG eBAYa://rRRasv.kPV/kWfpq-lqkk/Idris2/uLojXs/3651
uQF = %wandEvt nCjdTxdvgnNWbjtXSdpH (X (Fin 5) List) X'
  [ `(MkX [FZ, FS FZ] [5,6,7,8] ["9", "10"] [[0],[1],[2]])
  ]
