module ConsApps

import Infra

%default total

%language ElabReflection

public export
data X : Type -> Type -> Type where
  XX : Either a b -> X a b

%runElab printDeepConsApps $ pure
  [ `(Vect n Nat) @@@ ["n", "a"]
  , `(Vect n Nat) @@@ ["n"]
  , `(Vect n (Either a b)) @@@ ["n", "a", "b"]
  , `(Vect (S n) (Either a b)) @@@ ["n", "a", "b"]
  , `(Vect (S n) (Either a a)) @@@ ["n", "a", "b"]
  , `(Vect (S $ S n) (Either a (X a a))) @@@ ["n", "a", "b"]
  ]
