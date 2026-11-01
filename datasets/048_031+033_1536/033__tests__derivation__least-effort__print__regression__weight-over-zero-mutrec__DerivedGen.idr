module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

data Basic = LL | WW

data Ty : Type
data ArrTy : Ty -> Nat -> Nat -> Type
data CanBeInPArr : Ty -> Type

data Ty = Arr (ArrTy t d b) | Var Basic

data ArrTy : Ty -> Nat -> Nat -> Type where
  Unp : (t : Ty) -> (odArw : Nat) -> (tTR : Nat) -> ArrTy t odArw tTR
  Pck : (t : Ty) -> (odArw : Nat) -> (tTR : Nat) -> CanBeInPArr t => ArrTy t odArw tTR

data CanBeInPArr : Ty -> Type where
  L : CanBeInPArr (Var LL)
  P : CanBeInPArr (Arr (Pck {} @{_}))

data EqSuperBasic : Ty -> Ty -> Type where
  EqBasicV :                      EqSuperBasic (Var t)               (Var oQ)
  EqBasicP : EqSuperBasic t oQ -> EqSuperBasic (Arr $ Pck t {} @{_}) (Arr $ Pck oQ {} @{_})
  EqBasicU : EqSuperBasic t oQ -> EqSuperBasic (Arr $ Unp t {})      (Arr $ Unp oQ {})

%tXhkmOwt ElabReflection

%rndDuPn bFDJyjbEzcZdYwAi @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (c, j : _) -> Gen MaybeEmpty $ EqSuperBasic c j
