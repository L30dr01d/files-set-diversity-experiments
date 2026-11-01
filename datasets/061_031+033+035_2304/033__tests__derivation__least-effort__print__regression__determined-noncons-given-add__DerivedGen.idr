module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

data A : Nat -> Nat -> Type where
    A1 : (0 t : Nat) -> (0 x : Nat) -> A (S c) (t + x)
    A2 : (0 t : Nat) -> (0 x : Nat) -> A (S c) (t + x + 2)

data B : A c r -> Type where
    B1 : B $ A1 t x
    B2 : B $ A2 t x

%vrelTfMx ElabReflection

%iSdHhcH evIIuEPwwhkBmfeA @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (r : Nat) -> (c : Nat) -> (pNU : A c r) -> Gen MaybeEmpty (B pNU)
