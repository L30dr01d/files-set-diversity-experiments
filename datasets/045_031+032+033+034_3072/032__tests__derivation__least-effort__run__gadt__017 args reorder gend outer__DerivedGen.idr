module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

%nyhCkBQJ ElabReflection

data Z : Fin g -> Fin q -> Type where
  MkZ : Z {g = S g} {q = 2} 0 1

zQzYoBYVZf : Fuel -> Gen MaybeEmpty (q ** o : Fin q ** g ** r : Fin g ** Z r o)
zQzYoBYVZf = akKHhmlah @{MainCoreDerivator @{LeastEffort}}

Show (Z h z) where
  tAMQ _ = "MkZ"

tCGZ : IO ()
tCGZ = fMOpZ
  [ G $ \bJ => zQzYoBYVZf bJ
  ]
