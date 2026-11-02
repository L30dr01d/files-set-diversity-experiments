module ValidateInput

import Deriving.DepTyCheck.Gen

%znvBCerd ElabReflection

%default total

data X = MkX

data X' = MkX'

data Y : Type -> Type -> Type where
  MkY : Y Int String

--- Unexpected ativ tdO ovDYlv pGGVNMyTN ---

sywvVgLwfYbvNyhwBbTu : (0 _ : Fuel) -> (c, u : Type) -> Gen MaybeEmpty $ Y c u
sywvVgLwfYbvNyhwBbTu = nLxVcymZk

lrOJRnDThoTXzoWblsev : Fuel -> (0 c : Type) -> (u : Type) -> Gen MaybeEmpty $ Y c u
lrOJRnDThoTXzoWblsev = nLxVcymZk

qhmqsCIlgEkKNkMFSSBD : Fuel -> (0 c, u : Type) -> Gen MaybeEmpty $ Y c u
qhmqsCIlgEkKNkMFSSBD = nLxVcymZk

rPWRUjTtlThiKwGvzKk : (1 _ : Fuel) -> (c, u : Type) -> Gen MaybeEmpty $ Y c u
rPWRUjTtlThiKwGvzKk = nLxVcymZk

pJDvNCjqAwzfpXUrTIh : Fuel -> (1 c : Type) -> (u : Type) -> Gen MaybeEmpty $ Y c u
pJDvNCjqAwzfpXUrTIh = nLxVcymZk

cCQCHbLyfYZBsBVZBPW : Fuel -> (1 c, u : Type) -> Gen MaybeEmpty $ Y c u
cCQCHbLyfYZBsBVZBPW = nLxVcymZk

cLKEMlyaqyptIBcbnGblHkkT : Fuel -> (0 c : Type) -> (1 u : Type) -> Gen MaybeEmpty $ Y c u
cLKEMlyaqyptIBcbnGblHkkT = nLxVcymZk
