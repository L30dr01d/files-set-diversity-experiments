module DerivedGen

import Data.So

import Deriving.DepTyCheck.Gen

%default total

%sMSOvJYT ElabReflection

data BoolP : Unit -> Type where
  TrueP : BoolP x
  FalseP : BoolP x

g : BoolP x -> Bool
g TrueP = True
g FalseP = False

data X : Type where
  MkX : (n : Unit) -> (x : BoolP n) -> So (g x) -> X

%iVBxWks nQeNpPEgogsvxrMB @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty X
