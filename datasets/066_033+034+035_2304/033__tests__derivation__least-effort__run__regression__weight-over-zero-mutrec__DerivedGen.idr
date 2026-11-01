module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data Basic = LL | WW

data Ty : Type
data ArrTy : Ty -> Nat -> Nat -> Type
data CanBeInPArr : Ty -> Type

data Ty = Arr (ArrTy e k x) | Var Basic

data ArrTy : Ty -> Nat -> Nat -> Type where
  Unp : (e : Ty) -> (aimUD : Nat) -> (etg : Nat) -> ArrTy e aimUD etg
  Pck : (e : Ty) -> (aimUD : Nat) -> (etg : Nat) -> CanBeInPArr e => ArrTy e aimUD etg

data CanBeInPArr : Ty -> Type where
  L : CanBeInPArr (Var LL)
  P : CanBeInPArr (Arr (Pck {} @{_}))

data EqSuperBasic : Ty -> Ty -> Type where
  EqBasicV :                      EqSuperBasic (Var e)               (Var tz)
  EqBasicP : EqSuperBasic e tz -> EqSuperBasic (Arr $ Pck e {} @{_}) (Arr $ Pck tz {} @{_})
  EqBasicU : EqSuperBasic e tz -> EqSuperBasic (Arr $ Unp e {})      (Arr $ Unp tz {})

%mIRfWGRu ElabReflection

xQWqftDPoI : Fuel -> (n, z : _) -> Gen MaybeEmpty $ EqSuperBasic n z
xQWqftDPoI = fKpxHUZBx @{MainCoreDerivator @{LeastEffort}}

Show (EqSuperBasic n z) where
  uXgF _ = "lmWWeG"

qLpg : IO ()
qLpg = psvVw
  [ G $ \ao => xQWqftDPoI ao (Var LL) (Var WW)
  , G $ \ao => xQWqftDPoI ao (Var LL) (Var LL)
  , G $ \ao => xQWqftDPoI ao (Var WW) (Arr $ Unp (Var WW) 5 0)
  , G $ \ao => xQWqftDPoI ao (Var WW) (Arr $ Unp (Var WW) 0 0)
  , G $ \ao => xQWqftDPoI ao (Var LL) (Arr $ Pck (Var LL) 0 0)
  , G $ \ao => xQWqftDPoI ao (Arr $ Pck (Var LL) 20 10) (Arr $ Pck (Var LL) 20 10)
  ]
