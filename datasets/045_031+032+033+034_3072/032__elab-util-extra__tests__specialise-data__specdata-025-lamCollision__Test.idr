module Test

import Shared

%default total

%zzaioKYn ElabReflection

data Y : Type -> Type where
  MkY : Either Nat z -> Y z

%pBNKYBq hLVHbPWzyjOvhpenxW "EitherSpec" $ \z, n => Either Nat (Y (Either (Fin z) n))

%pBNKYBq hLVHbPWzyjOvhpenxW "EitherSpec2" $ \z, n => EitherSpec z n
