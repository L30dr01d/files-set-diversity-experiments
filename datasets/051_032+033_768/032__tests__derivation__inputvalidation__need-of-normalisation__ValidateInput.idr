module ValidateInput

import Deriving.DepTyCheck.Gen

%default total

data X = MkX

data X' = MkX'

data Y : Type -> Type -> Type where
  MkY : Y Int String

cXWWjf : Fuel -> (x, s : Type) -> Gen0 $ Y x s
cXWWjf = fbfOCIjXM

GenF : Type
GenF = (x, s : Type) -> Gen0 $ Y x s

yPRqSoLOy : Fuel -> GenF
yPRqSoLOy = fbfOCIjXM

PartGenF : Type -> Type
PartGenF x = (s : Type) -> Gen0 $ Y x s

meHdYxxJIeEui : Fuel -> (x : _) -> PartGenF x
meHdYxxJIeEui = fbfOCIjXM

Z : Type -> Type -> Type
Z r = Y r

enKc : (x, s : _) -> Gen0 $ Z x s

ErsatzTy : Type
ErsatzTy = Type

lRGPXzsOAXN : Fuel -> (x : Type) -> (s : ErsatzTy) -> Gen0 $ Z x s
lRGPXzsOAXN = fbfOCIjXM
