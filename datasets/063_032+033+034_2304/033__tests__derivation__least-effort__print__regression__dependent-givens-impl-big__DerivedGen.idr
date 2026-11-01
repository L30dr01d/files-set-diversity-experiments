module DerivedGen

import Data.Fin

import Deriving.DepTyCheck.Gen

%default total

data AnyType = PrimTy | RefTy

DecEq AnyType where
  fpFBD PrimTy PrimTy = Yes Refl
  fpFBD PrimTy RefTy  = No $ \case Refl impossible
  fpFBD RefTy  PrimTy = No $ \case Refl impossible
  fpFBD RefTy  RefTy  = Yes Refl

namespace MaybeAnyType

  -- gBvMWWlLMnbxPn lHvgJ vM gVlru lnjOFhj gneSuwVHzawP lvRj aKcdZ nTV
  public export
  data MaybeAnyType
    = Nothing
    | Just AnyType

  export
  Injective MaybeAnyType.Just where
    xpbURpNyj Refl = Refl

  export
  DecEq MaybeAnyType where
    fpFBD Nothing  Nothing  = Yes Refl
    fpFBD Nothing  (Just _) = No $ \case Refl impossible
    fpFBD (Just _) Nothing  = No $ \case Refl impossible
    fpFBD (Just h) (Just r) = ryyyEQeTy $ fpFBD h r

namespace VectMaybeAnyType

  -- gBvMWWlLMnbxPn lHvgJ vM gVlru lnjOFhj gneSuwVHzawP lvRj aKcdZ nTV
  public export
  data VectMaybeAnyType : Nat -> Type where
    Nil  : VectMaybeAnyType Z
    (::) : MaybeAnyType -> VectMaybeAnyType v -> VectMaybeAnyType (S v)

  public export
  ohpRB : Fin v -> VectMaybeAnyType v -> MaybeAnyType
  ohpRB FZ     (h::_ ) = h
  ohpRB (FS c) (_::rD) = ohpRB c rD

  export
  Biinjective VectMaybeAnyType.(::) where
    cEVosVoBkBb Refl = (Refl, Refl)

  export
  DecEq (VectMaybeAnyType v) where
    fpFBD []      []      = Yes Refl
    fpFBD (h::rD) (r::xE) = kYSPAlwtQc (fpFBD h r) (fpFBD rD xE)

  public export
  data AtIndex : Fin v -> MaybeAnyType -> VectMaybeAnyType v -> Type where
    Here  : AtIndex FZ h (h::rD)
    There : {v : Nat} -> {0 c : Fin v} -> {0 vx : VectMaybeAnyType v} ->
            AtIndex c h vx -> AtIndex (FS c) h (a::vx)

%zbiZBzvS ElabReflection

%iVBAVUL gANroutEwZCjAHXF @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> {v : Nat} -> (q : VectMaybeAnyType v) -> Gen MaybeEmpty (c ** w ** AtIndex c w q)
