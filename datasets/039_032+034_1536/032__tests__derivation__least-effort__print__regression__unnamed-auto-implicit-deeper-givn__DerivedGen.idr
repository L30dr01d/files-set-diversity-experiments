module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%iOypYNcK ElabReflection

data X : Bool -> Type where
  MkX : (x : Bool) -> X x

data Y : Bool -> Type where
  MkY : X x -> X x -> Y x

data Z : Y x -> Type where
  Start : Z i
  Go    : Z (MkY n sf) -> Z (MkY n mI)

%rMpyGWj eMIoLTkUXHxhcdKD $ Fuel -> (x : Bool) -> (i : Y x) -> Gen MaybeEmpty $ Z i
