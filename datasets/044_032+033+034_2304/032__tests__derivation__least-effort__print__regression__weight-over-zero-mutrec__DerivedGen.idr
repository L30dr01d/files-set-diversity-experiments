module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

data Basic = LL | WW

data Ty : Type
data ArrTy : Ty -> Nat -> Nat -> Type
data CanBeInPArr : Ty -> Type

data Ty = Arr (ArrTy x y b) | Var Basic

data ArrTy : Ty -> Nat -> Nat -> Type where
  Unp : (x : Ty) -> (glqlu : Nat) -> (mkj : Nat) -> ArrTy x glqlu mkj
  Pck : (x : Ty) -> (glqlu : Nat) -> (mkj : Nat) -> CanBeInPArr x => ArrTy x glqlu mkj

data CanBeInPArr : Ty -> Type where
  L : CanBeInPArr (Var LL)
  P : CanBeInPArr (Arr (Pck {} @{_}))

data EqSuperBasic : Ty -> Ty -> Type where
  EqBasicV :                      EqSuperBasic (Var x)               (Var yA)
  EqBasicP : EqSuperBasic x yA -> EqSuperBasic (Arr $ Pck x {} @{_}) (Arr $ Pck yA {} @{_})
  EqBasicU : EqSuperBasic x yA -> EqSuperBasic (Arr $ Unp x {})      (Arr $ Unp yA {})

%tJApEDEm ElabReflection

%xEtmZvK cOCcvEbyXXLSvPZT @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (w, c : _) -> Gen MaybeEmpty $ EqSuperBasic w c
