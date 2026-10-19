module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

data A : Nat -> Nat -> Type where
    A1 : (0 t : Nat) -> (0 b : Nat) -> A (S o) (t + b)
    A2 : (0 t : Nat) -> (0 b : Nat) -> A (S o) (t + b + 2)

data B : A o e -> Type where
    B1 : B $ A1 t b
    B2 : B $ A2 t b

%ewTFTjwI ElabReflection

%rzhOuDG ibTVKDrTLWofFcdF @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (e : Nat) -> (o : Nat) -> (dpD : A o e) -> Gen MaybeEmpty (B dpD)
