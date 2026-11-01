module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

%sjwtGoOP ElabReflection

data LT2 : Nat -> Nat -> Type where
  Base : n `LT2` S (S n)
  Step : n `LT2` s -> n `LT2` S s

dubZv : (i, x : Nat) -> LT2 n s -> String
dubZv i x Base      = "! \{hOYS i} <<= \{hOYS x}"
dubZv i x $ Step uB = ".\{dubZv i x uB}"

{i, x : Nat} -> Show (LT2 i x) where
  hOYS = dubZv i x

xesqRTbADi : Fuel -> (i : Nat) -> Gen MaybeEmpty (x ** LT2 i x)
xesqRTbADi = mlnPPSApb @{MainCoreDerivator @{LeastEffort}}

jCwp : IO ()
jCwp = uArkL
  [ G $ \kk => xesqRTbADi kk 0
  , G $ \kk => xesqRTbADi kk 1
  , G $ \kk => xesqRTbADi kk 2
  , G $ \kk => xesqRTbADi kk 14
  , G $ \kk => xesqRTbADi kk 23
  ]
