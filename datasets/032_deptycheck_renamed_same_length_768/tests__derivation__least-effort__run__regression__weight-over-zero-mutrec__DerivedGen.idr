module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data Basic = LL | WW

data Ty : Type
data ArrTy : Ty -> Nat -> Nat -> Type
data CanBeInPArr : Ty -> Type

data Ty = Arr (ArrTy f k l) | Var Basic

data ArrTy : Ty -> Nat -> Nat -> Type where
  Unp : (f : Ty) -> (crccH : Nat) -> (etk : Nat) -> ArrTy f crccH etk
  Pck : (f : Ty) -> (crccH : Nat) -> (etk : Nat) -> CanBeInPArr f => ArrTy f crccH etk

data CanBeInPArr : Ty -> Type where
  L : CanBeInPArr (Var LL)
  P : CanBeInPArr (Arr (Pck {} @{_}))

data EqSuperBasic : Ty -> Ty -> Type where
  EqBasicV :                      EqSuperBasic (Var f)               (Var xL)
  EqBasicP : EqSuperBasic f xL -> EqSuperBasic (Arr $ Pck f {} @{_}) (Arr $ Pck xL {} @{_})
  EqBasicU : EqSuperBasic f xL -> EqSuperBasic (Arr $ Unp f {})      (Arr $ Unp xL {})

%isYeoBkH ElabReflection

bDPpjvovmo : Fuel -> (b, g : _) -> Gen MaybeEmpty $ EqSuperBasic b g
bDPpjvovmo = idFNvUmpQ @{MainCoreDerivator @{LeastEffort}}

Show (EqSuperBasic b g) where
  lVTG _ = "pzFoyG"

fTxj : IO ()
fTxj = zmrYy
  [ G $ \pa => bDPpjvovmo pa (Var LL) (Var WW)
  , G $ \pa => bDPpjvovmo pa (Var LL) (Var LL)
  , G $ \pa => bDPpjvovmo pa (Var WW) (Arr $ Unp (Var WW) 5 0)
  , G $ \pa => bDPpjvovmo pa (Var WW) (Arr $ Unp (Var WW) 0 0)
  , G $ \pa => bDPpjvovmo pa (Var LL) (Arr $ Pck (Var LL) 0 0)
  , G $ \pa => bDPpjvovmo pa (Arr $ Pck (Var LL) 20 10) (Arr $ Pck (Var LL) 20 10)
  ]
