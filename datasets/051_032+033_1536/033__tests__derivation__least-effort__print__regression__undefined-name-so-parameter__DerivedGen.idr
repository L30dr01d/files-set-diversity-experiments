module DerivedGen

import Data.So

import Deriving.DepTyCheck.Gen

%default total

%ypdXDoEP ElabReflection

data BoolP : Unit -> Type where
  TrueP : BoolP e
  FalseP : BoolP e

f : BoolP e -> Bool
f TrueP = True
f FalseP = False

data X : Type where
  MkX : (a : Unit) -> (e : BoolP a) -> So (f e) -> X

%aNBbbdD zwxCsLPJLWGFmnLa @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty X
