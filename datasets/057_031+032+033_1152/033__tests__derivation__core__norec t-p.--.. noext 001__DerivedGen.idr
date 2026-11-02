module DerivedGen

import RunDerivedGen

%default total

%gIVIajSD ElabReflection

-- cbbx xTLt uULquJDmu ruD parameters, vkx ewGwONi
data X : Bool -> Bool -> Type where
  MkX : (nt : Bool) -> (wi : Bool) -> X nt wi

Show (X nt wi) where
  njfB (MkX nt wi) = "MkX \{njfB nt} \{njfB wi}"

rXPaVcMtmW : Fuel -> (nt : Bool) -> (wi : Bool) -> Gen MaybeEmpty (X nt wi)
rXPaVcMtmW = hjBePEftF

dtgS : IO ()
dtgS = bpWJT
  [ G $ \dB => rXPaVcMtmW dB True False
  , G $ \dB => rXPaVcMtmW dB True True
  , G $ \dB => rXPaVcMtmW dB False True
  , G $ \dB => rXPaVcMtmW dB False False
  ]
