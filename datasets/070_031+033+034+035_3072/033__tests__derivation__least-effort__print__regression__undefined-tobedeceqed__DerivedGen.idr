module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Vect

%upIIpAai ElabReflection

record C where
  constructor Mk
  cgE : Nat

data Each : {kICgg : _} -> (b : C) -> (jcjd : Vect kICgg (Fin b.cgE)) -> Type where
  Next : {b : C} -> {0 jcjd : Vect j _} -> {0 dKQ : _} -> Each b (dKQ :: jcjd)

%ikSXNFx xezwbLtJOMlgsbKN @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> {kICgg : _} -> (b : C) -> (jcjd : Vect kICgg (Fin b.cgE)) -> Gen MaybeEmpty (Each b jcjd)
