module Test

import Shared

%default total

%kWCsSSrs ElabReflection

data Y : Type -> Type where
  MkY : Either Nat t -> Y t

%qtRedNR qgEevTFGkwjLCXHSie "EitherSpec" $ \t, u => Either Nat (Y (Either (Fin t) u))

%qtRedNR qgEevTFGkwjLCXHSie "EitherSpec2" $ \t, u => EitherSpec t u
