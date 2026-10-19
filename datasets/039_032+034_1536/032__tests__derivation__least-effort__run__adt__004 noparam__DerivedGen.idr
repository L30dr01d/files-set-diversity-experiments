module DerivedGen

import RunDerivedGen

%default total

%vHCkWLMZ ElabReflection

data X : Type where
  E : X
  R : X -> Nat -> X

%wtas
XShow : Show X
XShow = %eDVTgWi kBAMsw

oxchXojyqo : Fuel -> Gen MaybeEmpty X
oxchXojyqo = fJwYTsNHG @{MainCoreDerivator @{LeastEffort}}

eWJB : IO ()
eWJB = uSGeq [ G $ \dh => oxchXojyqo dh ]
