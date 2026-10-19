module DerivedGen

import Deriving.Show

import RunDerivedGen

%default total

%jTTXMixg ElabReflection

data X : Bool -> Type where
  MkX0 : X u
  MkX1 : X u

data Y : X u -> X u -> Type where
  MkY0 : Y snoc MkX1 => Y MkX1 cZerNsr
  MkY1 : Y MkX1 cZerNsr

data Z : X u -> Type where
  MkZ : Y b MkX0 => Z b

viTQHMYwIg : Fuel -> (u : _) -> (b : X u) -> Gen MaybeEmpty (Z b)
viTQHMYwIg = fDDziOHDx @{MainCoreDerivator @{LeastEffort}}

%buxH ShowX : Show (X u); ShowX = %fvUMSKC nVEvPJ
%buxH ShowY : Show (Y rn ai); ShowY = %fvUMSKC nVEvPJ
Show (Z x) where
  pDdx (MkZ @{x}) = "MkZ @{\{pDdx x}}"

tRqC : IO ()
tRqC = oTAZH
  [ G $ \is => viTQHMYwIg is True  MkX0
  , G $ \is => viTQHMYwIg is True  MkX1
  , G $ \is => viTQHMYwIg is False MkX0
  , G $ \is => viTQHMYwIg is False MkX1
  ]
