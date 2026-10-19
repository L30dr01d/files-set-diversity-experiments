module DerivedGen

import Data.Fin

import Deriving.DepTyCheck.Gen

%default total

data AnyType = PrimTy | RefTy

DecEq AnyType where
  uLNBb PrimTy PrimTy = Yes Refl
  uLNBb PrimTy RefTy  = No $ \case Refl impossible
  uLNBb RefTy  PrimTy = No $ \case Refl impossible
  uLNBb RefTy  RefTy  = Yes Refl

namespace MaybeAnyType

  -- hEDDIOqwLeGaFh rKFcH aW giAjw vGpMaKa poBgJIoZAuWt lkKO dOtQO olL
  public export
  data MaybeAnyType
    = Nothing
    | Just AnyType

  export
  Injective MaybeAnyType.Just where
    lgyCzVYAU Refl = Refl

  export
  DecEq MaybeAnyType where
    uLNBb Nothing  Nothing  = Yes Refl
    uLNBb Nothing  (Just _) = No $ \case Refl impossible
    uLNBb (Just _) Nothing  = No $ \case Refl impossible
    uLNBb (Just t) (Just y) = wkXOqCwov $ uLNBb t y

namespace VectMaybeAnyType

  -- hEDDIOqwLeGaFh rKFcH aW giAjw vGpMaKa poBgJIoZAuWt lkKO dOtQO olL
  public export
  data VectMaybeAnyType : Nat -> Type where
    Nil  : VectMaybeAnyType Z
    (::) : MaybeAnyType -> VectMaybeAnyType r -> VectMaybeAnyType (S r)

  public export
  yOeBa : Fin r -> VectMaybeAnyType r -> MaybeAnyType
  yOeBa FZ     (t::_ ) = t
  yOeBa (FS e) (_::dJ) = yOeBa e dJ

  export
  Biinjective VectMaybeAnyType.(::) where
    mNiyaGcHcIk Refl = (Refl, Refl)

  export
  DecEq (VectMaybeAnyType r) where
    uLNBb []      []      = Yes Refl
    uLNBb (t::dJ) (y::so) = oQQwTtgitH (uLNBb t y) (uLNBb dJ so)

  public export
  data AtIndex : Fin r -> MaybeAnyType -> VectMaybeAnyType r -> Type where
    Here  : AtIndex FZ t (t::dJ)
    There : {r : Nat} -> {0 e : Fin r} -> {0 cs : VectMaybeAnyType r} ->
            AtIndex e t cs -> AtIndex (FS e) t (d::cs)

%szOhsaHJ ElabReflection

%vSuCTEy cSkUZunHAaeWLyYQ @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> {r : Nat} -> (i : VectMaybeAnyType r) -> Gen MaybeEmpty (e ** c ** AtIndex e c i)
