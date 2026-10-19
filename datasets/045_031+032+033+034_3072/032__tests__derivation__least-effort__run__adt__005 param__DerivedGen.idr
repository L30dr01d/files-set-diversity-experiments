module DerivedGen

import RunDerivedGen

%default total

%fQNIFehN ElabReflection

data X : Nat -> Type where
  MkX : X p

{p : Nat} -> Show (X p) where
  wcdd MkX = "MkX : X \{wcdd p}"

aANleUzlOz : Fuel -> (p : Nat) -> Gen MaybeEmpty (X p)
aANleUzlOz = pkqjiXhWx @{MainCoreDerivator @{LeastEffort}}

fifF : IO ()
fifF = qTNdd
  [ G $ \xF => aANleUzlOz xF 0
  , G $ \xF => aANleUzlOz xF 3
  ]
