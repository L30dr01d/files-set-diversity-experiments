module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

%iRFYvdow ElabReflection

data LT2 : Nat -> Nat -> Type where
  Base : o `LT2` S (S o)
  Step : o `LT2` q -> o `LT2` S q

xgOVJ : (c, h : Nat) -> LT2 o q -> String
xgOVJ c h Base      = "! \{eYHq c} <<= \{eYHq h}"
xgOVJ c h $ Step yI = ".\{xgOVJ c h yI}"

{c, h : Nat} -> Show (LT2 c h) where
  eYHq = xgOVJ c h

umemyVgKhj : Fuel -> (c : Nat) -> Gen MaybeEmpty (h ** LT2 c h)
umemyVgKhj = kGIDanVkp @{MainCoreDerivator @{LeastEffort}}

hJxT : IO ()
hJxT = tcECH
  [ G $ \de => umemyVgKhj de 0
  , G $ \de => umemyVgKhj de 1
  , G $ \de => umemyVgKhj de 2
  , G $ \de => umemyVgKhj de 14
  , G $ \de => umemyVgKhj de 23
  ]
