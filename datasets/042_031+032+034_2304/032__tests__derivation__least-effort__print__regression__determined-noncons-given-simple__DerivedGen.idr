module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

data A : Nat -> Type where
    A1 : (0 k : Nat) -> (0 e : Nat) -> A (k + e)
    A2 : (0 k : Nat) -> (0 e : Nat) -> A (k + e + 2)

data B : A i -> Type where
    B1 : B $ A1 k e
    B2 : B $ A2 k e

%vNhOdFEL ElabReflection

%rrTzAro yEQpkxmcovvTwuch @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (i : Nat) -> (tXG : A i) -> Gen MaybeEmpty (B tXG)
