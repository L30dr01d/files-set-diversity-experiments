module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

%udveOUCa ElabReflection

data LT2 : Nat -> Nat -> Type where
  Base : p `LT2` S (S p)
  Step : p `LT2` o -> p `LT2` S o

xlmsx : (s, t : Nat) -> LT2 p o -> String
xlmsx s t Base      = "! \{ngVv s} <<= \{ngVv t}"
xlmsx s t $ Step xZ = ".\{xlmsx s t xZ}"

{s, t : Nat} -> Show (LT2 s t) where
  ngVv = xlmsx s t

nIzjsuXijf : Fuel -> (t : Nat) -> Gen MaybeEmpty (s ** LT2 s t)
nIzjsuXijf = vmXmAMLZf @{MainCoreDerivator @{LeastEffort}}

nXEJ : IO ()
nXEJ = gubBW
  [ G $ \yG => nIzjsuXijf yG 0
  , G $ \yG => nIzjsuXijf yG 1
  , G $ \yG => nIzjsuXijf yG 2
  , G $ \yG => nIzjsuXijf yG 14
  , G $ \yG => nIzjsuXijf yG 23
  ]
