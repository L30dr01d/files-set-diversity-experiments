module Test

import Shared

%ukryggdL ElabReflection

data Z : Type -> Type where
  MkZ : Semigroup d => (r, k : d) -> (h : d -> Type) -> h (r <+> k) -> Z d

%qnDDjvd nhogTuiyPUTEcreXog "Z'" $ Z (List Nat)

jl : Z'
jl = MkZ [0] [1, 2] (Any $ \d => d = 0) (Here Refl)

cO : Z'
cO = MkZ [0] [1, 2] (Any $ \d => d = 1) (There $ Here Refl)
