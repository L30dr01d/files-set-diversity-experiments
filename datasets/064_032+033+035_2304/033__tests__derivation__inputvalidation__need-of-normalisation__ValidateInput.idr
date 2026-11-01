module ValidateInput

import Deriving.DepTyCheck.Gen

%default total

data X = MkX

data X' = MkX'

data Y : Type -> Type -> Type where
  MkY : Y Int String

tapPBs : Fuel -> (q, z : Type) -> Gen0 $ Y q z
tapPBs = wnnWVpPkU

GenF : Type
GenF = (q, z : Type) -> Gen0 $ Y q z

wbQHOmNyp : Fuel -> GenF
wbQHOmNyp = wnnWVpPkU

PartGenF : Type -> Type
PartGenF q = (z : Type) -> Gen0 $ Y q z

kgfpetHitbyKx : Fuel -> (q : _) -> PartGenF q
kgfpetHitbyKx = wnnWVpPkU

Z : Type -> Type -> Type
Z j = Y j

nqWF : (q, z : _) -> Gen0 $ Z q z

ErsatzTy : Type
ErsatzTy = Type

fUwTznDgESk : Fuel -> (q : Type) -> (z : ErsatzTy) -> Gen0 $ Z q z
fUwTznDgESk = wnnWVpPkU
