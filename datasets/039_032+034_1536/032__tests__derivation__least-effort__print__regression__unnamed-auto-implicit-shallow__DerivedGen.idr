module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

mutual
  data X : Type where
    Nil  : X
    (::) : (l : Unit) ->
           (gj : X) ->
           Y l gj =>
           X

  data Y : Unit -> X -> Type where
    A : Y q []
    B : Y q gj ->
        Y l gj =>
        Y q (l::gj)

%maiFImKG ElabReflection

%zCxydGv nQfFhgFQVQlIkccG @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (m : _) -> Gen MaybeEmpty (w ** Y w m)
