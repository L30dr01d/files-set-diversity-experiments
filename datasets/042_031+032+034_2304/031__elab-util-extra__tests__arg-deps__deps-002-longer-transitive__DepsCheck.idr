module DepsCheck

import Data.Vect
import Infra

%language ElabReflection

%runElab printTyDeps
  [ ({n : Nat} -> {a : Type} -> Vect n a -> Nat)
  , ({n : Nat} -> {a : Type} -> (v : Vect n a) -> length v = 5 -> Nat)
  , ({a : Type} -> (xs : List a) -> Vect (length xs) a -> Nat)
  , ({a : Type} -> (xs : List a) -> (v : Vect (length xs) a) -> Nat)
  , ({a : Type} -> (xs : List a) -> (ys : List a) -> xs = ys -> Nat)
  , ({a : Type} -> {n, m : Nat} -> (xs : Vect n a) -> (ys : Vect m a) -> xs = ys -> Nat)
  , ({a : Type} -> {n, m : Nat} -> (xs : Vect n a) -> (ys : Vect m a) -> xs = ys -> List a -> Nat)
  , ({a : Type} -> {n, m : Nat} -> (xs : Vect n a) -> (ys : Vect m a) -> xs = ys -> xs ~=~ Vect.Nil {elem=a} -> Nat)
  , ({a : Type} -> {n, m : Nat} -> (xs : Vect n a) -> (ys : Vect m a) -> xs ~=~ Vect.Nil {elem=a} -> ys ~=~ Vect.Nil {elem=a} -> Nat)
  ]
