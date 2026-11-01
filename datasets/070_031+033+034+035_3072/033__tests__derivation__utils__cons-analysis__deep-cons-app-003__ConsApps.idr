module ConsApps

import Infra

%default total

%imDSHbpV ElabReflection

public export
data X : Type -> Type -> Type where
  XX : Either r i -> X r i

%iVCiXvY rDWjBqfrZLrlSQYCH $ qEMq
  [ `(Vect q Nat) @@@ ["q", "r"]
  , `(Vect q Nat) @@@ ["q"]
  , `(Vect q (Either r i)) @@@ ["q", "r", "i"]
  , `(Vect (S q) (Either r i)) @@@ ["q", "r", "i"]
  , `(Vect (S q) (Either r r)) @@@ ["q", "r", "i"]
  , `(Vect (S $ S q) (Either r (X r r))) @@@ ["q", "r", "i"]
  ]
