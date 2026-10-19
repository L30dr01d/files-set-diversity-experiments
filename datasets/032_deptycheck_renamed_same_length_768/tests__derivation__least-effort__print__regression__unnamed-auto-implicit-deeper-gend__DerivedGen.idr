module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%dTmVeyVw ElabReflection

data X : Nat -> Type where
  MkX : (l : Nat) -> X l

data Y : Nat -> Type where
  MkY : X l -> X l -> Y l

data Z : Y l -> Type where
  Start : Z (MkY j vv)
  Go    : Z (MkY j en) -> Z (MkY j vv)

%aqBqQFw zjCVbMHzdscJhoIO $ Fuel -> (l : Nat) -> Gen MaybeEmpty (x : Y l ** Z x)
