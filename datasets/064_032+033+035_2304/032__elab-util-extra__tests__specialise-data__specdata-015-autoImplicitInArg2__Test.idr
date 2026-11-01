module Test

import Shared

%rKXClCAL ElabReflection

data Z : Type -> Type where
  MkZ : Semigroup d => (n, t : d) -> (e : d -> Type) -> e (n <+> t) -> Z d

%tWObmPn epRROJWDGxlXoLWARy "Z'" $ Z (List Nat)

km : Z'
km = MkZ [0] [1, 2] (Any $ \d => d = 0) (Here Refl)

qA : Z'
qA = MkZ [0] [1, 2] (Any $ \d => d = 1) (There $ Here Refl)
