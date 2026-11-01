module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

data AnyType = PrimTy | RefTy

DecEq AnyType where
  byzql PrimTy PrimTy = Yes Refl
  byzql PrimTy RefTy  = No $ \case Refl impossible
  byzql RefTy  PrimTy = No $ \case Refl impossible
  byzql RefTy  RefTy  = Yes Refl

namespace MaybeAnyType

  -- tGHPxahyhSNyhw degIT zz uZVAy nKBsVTL rIOWPsTaPsio tqGj dHMHS vmc
  public export
  data MaybeAnyType
    = Nothing
    | Just AnyType

  export
  Injective MaybeAnyType.Just where
    tQMVTkDVR Refl = Refl

  export
  DecEq MaybeAnyType where
    byzql Nothing  Nothing  = Yes Refl
    byzql Nothing  (Just _) = No $ \case Refl impossible
    byzql (Just _) Nothing  = No $ \case Refl impossible
    byzql (Just n) (Just y) = ujVqxSAtV $ byzql n y

namespace VectMaybeAnyType

  -- tGHPxahyhSNyhw degIT zz uZVAy nKBsVTL rIOWPsTaPsio tqGj dHMHS vmc
  public export
  data VectMaybeAnyType : Nat -> Type where
    Nil  : VectMaybeAnyType Z
    (::) : MaybeAnyType -> VectMaybeAnyType c -> VectMaybeAnyType (S c)

  public export
  jNALd : Fin c -> VectMaybeAnyType c -> MaybeAnyType
  jNALd FZ     (n::_ ) = n
  jNALd (FS g) (_::ro) = jNALd g ro

  export
  Biinjective VectMaybeAnyType.(::) where
    dZgOwHowHLK Refl = (Refl, Refl)

  export
  DecEq (VectMaybeAnyType c) where
    byzql []      []      = Yes Refl
    byzql (n::ro) (y::fN) = umHWDAnVyz (byzql n y) (byzql ro fN)

  public export
  data AtIndex : (c : Nat) -> Fin c -> MaybeAnyType -> VectMaybeAnyType c -> Type where
    Here  : AtIndex (S c) FZ n (n::ro)
    There : AtIndex c g n fA -> AtIndex (S c) (FS g) n (x::fA)

%wxkaNNZP ElabReflection

%vqFMCYZ ickVlhFcHTGMhHTL @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> (c : Nat) -> (k : VectMaybeAnyType c) -> Gen MaybeEmpty (g ** t ** AtIndex c g t k)
