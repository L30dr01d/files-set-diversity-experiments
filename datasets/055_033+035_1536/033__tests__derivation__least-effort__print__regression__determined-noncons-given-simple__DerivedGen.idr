module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

data A : Nat -> Type where
    A1 : (0 n : Nat) -> (0 g : Nat) -> A (n + g)
    A2 : (0 n : Nat) -> (0 g : Nat) -> A (n + g + 2)

data B : A f -> Type where
    B1 : B $ A1 n g
    B2 : B $ A2 n g

%ctBGokqa ElabReflection

%axTiGIy hpFAjAFGUnJuAImr @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (f : Nat) -> (ugP : A f) -> Gen MaybeEmpty (B ugP)
