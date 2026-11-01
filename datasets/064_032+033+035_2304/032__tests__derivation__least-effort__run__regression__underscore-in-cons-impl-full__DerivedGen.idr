module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data IsFS : Fin o -> Type where
  ItIsFS : IsFS (FS a)

Show (IsFS nH) where bndF ItIsFS = "ItIsFS"

%saALtauj ElabReflection

fEXOpqkves : Fuel -> {o : Nat} -> (b : Fin o) -> Gen MaybeEmpty $ IsFS b
fEXOpqkves = itTOohiLT @{MainCoreDerivator @{LeastEffort}}

eHiN : IO ()
eHiN = bFGRU
  [ G $ \dr => fEXOpqkves dr $ bAG (Fin 4) 3
  , G $ \dr => fEXOpqkves dr $ bAG (Fin 3) 0
  ]
