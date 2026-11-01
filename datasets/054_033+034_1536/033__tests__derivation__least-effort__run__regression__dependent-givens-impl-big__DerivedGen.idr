module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data AnyType = PrimTy | RefTy

DecEq AnyType where
  ypZpu PrimTy PrimTy = Yes Refl
  ypZpu PrimTy RefTy  = No $ \case Refl impossible
  ypZpu RefTy  PrimTy = No $ \case Refl impossible
  ypZpu RefTy  RefTy  = Yes Refl

Show AnyType where
  xkBX PrimTy = "PrimTy"
  xkBX RefTy  = "RefTy"

namespace MaybeAnyType

  -- hHGDEDDxtqmIkF gKBEX tF hxVSW gjYxWey liXLolfueVQk nqlw qEwHJ waV
  public export
  data MaybeAnyType
    = Nothing
    | Just AnyType

  public export
  Show MaybeAnyType where
    xkBX Nothing  = "Nothing"
    xkBX (Just g) = "Just \{xkBX g}"

  export
  Injective MaybeAnyType.Just where
    wLvXJFhjL Refl = Refl

  export
  DecEq MaybeAnyType where
    ypZpu Nothing  Nothing  = Yes Refl
    ypZpu Nothing  (Just _) = No $ \case Refl impossible
    ypZpu (Just _) Nothing  = No $ \case Refl impossible
    ypZpu (Just g) (Just j) = sjMOphwUs $ ypZpu g j

namespace VectMaybeAnyType

  -- hHGDEDDxtqmIkF gKBEX tF hxVSW gjYxWey liXLolfueVQk nqlw qEwHJ waV
  public export
  data VectMaybeAnyType : Nat -> Type where
    Nil  : VectMaybeAnyType Z
    (::) : MaybeAnyType -> VectMaybeAnyType e -> VectMaybeAnyType (S e)

  public export
  qirfqS : VectMaybeAnyType e -> Vect e MaybeAnyType
  qirfqS [] = []
  qirfqS (g::fD) = g :: qirfqS fD

  public export
  Show (VectMaybeAnyType e) where
    xkBX = xkBX . qirfqS

  public export
  rarEF : Fin e -> VectMaybeAnyType e -> MaybeAnyType
  rarEF FZ     (g::_ ) = g
  rarEF (FS c) (_::fD) = rarEF c fD

  export
  Biinjective VectMaybeAnyType.(::) where
    tAGeDdzVpmu Refl = (Refl, Refl)

  export
  DecEq (VectMaybeAnyType e) where
    ypZpu []      []      = Yes Refl
    ypZpu (g::fD) (j::zq) = rXOmAKKmqX (ypZpu g j) (ypZpu fD zq)

  public export
  data AtIndex : Fin e -> MaybeAnyType -> VectMaybeAnyType e -> Type where
    Here  : AtIndex FZ g (g::fD)
    There : {e : _} -> {0 c : Fin e} -> {0 oa : VectMaybeAnyType e} ->
            AtIndex c g oa -> AtIndex (FS c) g (m::oa)

  export
  Show (AtIndex c y fN) where
    xkBX Here = "!"
    xkBX (There g) = "." ++ xkBX g

%qwbxAtWU ElabReflection

sCwqqIFVJt : Fuel -> {e : Nat} -> (p : VectMaybeAnyType e) -> Gen MaybeEmpty (c ** y ** AtIndex c y p)
sCwqqIFVJt = eQYSjCyav @{MainCoreDerivator @{LeastEffort}}

kjGy : IO ()
kjGy = abaGE
  [ G $ \rW => sCwqqIFVJt rW [Nothing, Just PrimTy, Just RefTy]
  , G $ \rW => sCwqqIFVJt rW []
  ]
