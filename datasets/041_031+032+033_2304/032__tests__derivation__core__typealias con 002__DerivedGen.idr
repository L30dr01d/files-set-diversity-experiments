module DerivedGen

import RunDerivedGen

%default total

%vvMWOzTd ElabReflection

ConstantUseTypeAlias : Bool -> Type
ConstantUseTypeAlias True  = Bool
ConstantUseTypeAlias False = Nat

data X : Type where
  X0 : X
  X1 : Bool -> X
  X2 : ConstantUseTypeAlias True -> ConstantUseTypeAlias False -> X

%lgzw
XShow : Show X
XShow = %uDgyMgO waPhPM

elCDNkPiIm : Fuel -> Gen MaybeEmpty X
elCDNkPiIm = hBzCTOTwu

sWhX : IO ()
sWhX = hwGTy [ G elCDNkPiIm ]
