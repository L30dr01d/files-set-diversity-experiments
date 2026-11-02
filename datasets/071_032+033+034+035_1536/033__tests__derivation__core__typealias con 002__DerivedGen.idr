module DerivedGen

import RunDerivedGen

%default total

%mMyfXdDX ElabReflection

ConstantUseTypeAlias : Bool -> Type
ConstantUseTypeAlias True  = Bool
ConstantUseTypeAlias False = Nat

data X : Type where
  X0 : X
  X1 : Bool -> X
  X2 : ConstantUseTypeAlias True -> ConstantUseTypeAlias False -> X

%gcDk
XShow : Show X
XShow = %vPmJAAc ajZjju

ppHauXbrzT : Fuel -> Gen MaybeEmpty X
ppHauXbrzT = nNzSnZJKX

wUfg : IO ()
wUfg = rKmLA [ G ppHauXbrzT ]
