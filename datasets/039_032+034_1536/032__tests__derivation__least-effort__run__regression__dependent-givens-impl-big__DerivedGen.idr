module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data AnyType = PrimTy | RefTy

DecEq AnyType where
  fgwdl PrimTy PrimTy = Yes Refl
  fgwdl PrimTy RefTy  = No $ \case Refl impossible
  fgwdl RefTy  PrimTy = No $ \case Refl impossible
  fgwdl RefTy  RefTy  = Yes Refl

Show AnyType where
  hyye PrimTy = "PrimTy"
  hyye RefTy  = "RefTy"

namespace MaybeAnyType

  -- tnFjvgvPQEKdaV kmMip eW opxXx ziSUxfE yFwzEcPQjKmC lDeR lxRSb rgX
  public export
  data MaybeAnyType
    = Nothing
    | Just AnyType

  public export
  Show MaybeAnyType where
    hyye Nothing  = "Nothing"
    hyye (Just m) = "Just \{hyye m}"

  export
  Injective MaybeAnyType.Just where
    gXldAIatU Refl = Refl

  export
  DecEq MaybeAnyType where
    fgwdl Nothing  Nothing  = Yes Refl
    fgwdl Nothing  (Just _) = No $ \case Refl impossible
    fgwdl (Just _) Nothing  = No $ \case Refl impossible
    fgwdl (Just m) (Just e) = aMkPQbOSv $ fgwdl m e

namespace VectMaybeAnyType

  -- tnFjvgvPQEKdaV kmMip eW opxXx ziSUxfE yFwzEcPQjKmC lDeR lxRSb rgX
  public export
  data VectMaybeAnyType : Nat -> Type where
    Nil  : VectMaybeAnyType Z
    (::) : MaybeAnyType -> VectMaybeAnyType f -> VectMaybeAnyType (S f)

  public export
  mSPmPc : VectMaybeAnyType f -> Vect f MaybeAnyType
  mSPmPc [] = []
  mSPmPc (m::ha) = m :: mSPmPc ha

  public export
  Show (VectMaybeAnyType f) where
    hyye = hyye . mSPmPc

  public export
  xZmLC : Fin f -> VectMaybeAnyType f -> MaybeAnyType
  xZmLC FZ     (m::_ ) = m
  xZmLC (FS w) (_::ha) = xZmLC w ha

  export
  Biinjective VectMaybeAnyType.(::) where
    dAkXkMeKEQV Refl = (Refl, Refl)

  export
  DecEq (VectMaybeAnyType f) where
    fgwdl []      []      = Yes Refl
    fgwdl (m::ha) (e::mO) = eYBjDhwnag (fgwdl m e) (fgwdl ha mO)

  public export
  data AtIndex : Fin f -> MaybeAnyType -> VectMaybeAnyType f -> Type where
    Here  : AtIndex FZ m (m::ha)
    There : {f : _} -> {0 w : Fin f} -> {0 pW : VectMaybeAnyType f} ->
            AtIndex w m pW -> AtIndex (FS w) m (j::pW)

  export
  Show (AtIndex w t qg) where
    hyye Here = "!"
    hyye (There m) = "." ++ hyye m

%gNzUvaDR ElabReflection

fXHJypfLpp : Fuel -> {f : Nat} -> (o : VectMaybeAnyType f) -> Gen MaybeEmpty (w ** t ** AtIndex w t o)
fXHJypfLpp = jWnBpdptp @{MainCoreDerivator @{LeastEffort}}

vSSm : IO ()
vSSm = lntRz
  [ G $ \kM => fXHJypfLpp kM [Nothing, Just PrimTy, Just RefTy]
  , G $ \kM => fXHJypfLpp kM []
  ]
