module Test

import Shared

%default total

%iiMRcihT ElabReflection

data X : (f : Nat) -> Fin f -> Type where
  MkX : X 5 4

%iaiLYMd rIdkYnVJPpOryYjvpR "Y" $ \n, s => X n s
