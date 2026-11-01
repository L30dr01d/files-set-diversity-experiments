module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%tQufyUUd ElabReflection

data X : Nat -> Type where
  MkX : (m : Nat) -> X m

data Y : Nat -> Type where
  MkY : X m -> X m -> Y m

data Z : Y m -> Type where
  Start : Z (MkY b mI)
  Go    : Z (MkY b gN) -> Z (MkY b mI)

%tCnMfpw pNoYqPWnGoLKnOTU $ Fuel -> (m : Nat) -> Gen MaybeEmpty (p : Y m ** Z p)
