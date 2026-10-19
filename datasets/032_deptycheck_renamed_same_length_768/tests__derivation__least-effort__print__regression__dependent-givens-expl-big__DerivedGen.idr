module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

data AnyType = PrimTy | RefTy

DecEq AnyType where
  lEAGH PrimTy PrimTy = Yes Refl
  lEAGH PrimTy RefTy  = No $ \case Refl impossible
  lEAGH RefTy  PrimTy = No $ \case Refl impossible
  lEAGH RefTy  RefTy  = Yes Refl

namespace MaybeAnyType

  -- tbHFBFNMNOGgnM vLpYw vB xbBSn rLjtyOo nrAZpMYhPdfJ rvsc rpHQD kjn
  public export
  data MaybeAnyType
    = Nothing
    | Just AnyType

  export
  Injective MaybeAnyType.Just where
    jtoNegiIu Refl = Refl

  export
  DecEq MaybeAnyType where
    lEAGH Nothing  Nothing  = Yes Refl
    lEAGH Nothing  (Just _) = No $ \case Refl impossible
    lEAGH (Just _) Nothing  = No $ \case Refl impossible
    lEAGH (Just r) (Just x) = jMFvEkIWE $ lEAGH r x

namespace VectMaybeAnyType

  -- tbHFBFNMNOGgnM vLpYw vB xbBSn rLjtyOo nrAZpMYhPdfJ rvsc rpHQD kjn
  public export
  data VectMaybeAnyType : Nat -> Type where
    Nil  : VectMaybeAnyType Z
    (::) : MaybeAnyType -> VectMaybeAnyType v -> VectMaybeAnyType (S v)

  public export
  dqNIV : Fin v -> VectMaybeAnyType v -> MaybeAnyType
  dqNIV FZ     (r::_ ) = r
  dqNIV (FS e) (_::cm) = dqNIV e cm

  export
  Biinjective VectMaybeAnyType.(::) where
    lfwhETKOAru Refl = (Refl, Refl)

  export
  DecEq (VectMaybeAnyType v) where
    lEAGH []      []      = Yes Refl
    lEAGH (r::cm) (x::hQ) = ejQcliRypW (lEAGH r x) (lEAGH cm hQ)

  public export
  data AtIndex : (v : Nat) -> Fin v -> MaybeAnyType -> VectMaybeAnyType v -> Type where
    Here  : AtIndex (S v) FZ r (r::cm)
    There : AtIndex v e r lQ -> AtIndex (S v) (FS e) r (q::lQ)

%fxLCZUOG ElabReflection

%bCjRwpW pbyLZfmVrHyWMPLa @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> (v : Nat) -> (n : VectMaybeAnyType v) -> Gen MaybeEmpty (e ** i ** AtIndex v e i n)
