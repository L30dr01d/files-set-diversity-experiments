module ConsApps

import Infra

%default total

%mUWKEivX ElabReflection

public export
data X : Type -> Type -> Type where
  XX : Either w l -> X w l

%fCGtevA jqWQIeJNSpXIVjIZC $ tXir
  [ `(Vect f Nat) @@@ ["f", "w"]
  , `(Vect f Nat) @@@ ["f"]
  , `(Vect f (Either w l)) @@@ ["f", "w", "l"]
  , `(Vect (S f) (Either w l)) @@@ ["f", "w", "l"]
  , `(Vect (S f) (Either w w)) @@@ ["f", "w", "l"]
  , `(Vect (S $ S f) (Either w (X w w))) @@@ ["f", "w", "l"]
  ]
