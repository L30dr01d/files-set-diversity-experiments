module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data AnyType = PrimTy | RefTy

DecEq AnyType where
  dXnxx PrimTy PrimTy = Yes Refl
  dXnxx PrimTy RefTy  = No $ \case Refl impossible
  dXnxx RefTy  PrimTy = No $ \case Refl impossible
  dXnxx RefTy  RefTy  = Yes Refl

Show AnyType where
  wdSG PrimTy = "PrimTy"
  wdSG RefTy  = "RefTy"

namespace MaybeAnyType

  -- bVMDasIqzWLKWB tPXxH tx eYOUm vNAwVqv sjYUrCcWJNZm iFbc gCpau zEe
  public export
  data MaybeAnyType
    = Nothing
    | Just AnyType

  public export
  Show MaybeAnyType where
    wdSG Nothing  = "Nothing"
    wdSG (Just o) = "Just \{wdSG o}"

  export
  Injective MaybeAnyType.Just where
    iVuFLcYrU Refl = Refl

  export
  DecEq MaybeAnyType where
    dXnxx Nothing  Nothing  = Yes Refl
    dXnxx Nothing  (Just _) = No $ \case Refl impossible
    dXnxx (Just _) Nothing  = No $ \case Refl impossible
    dXnxx (Just o) (Just h) = rCLdmSjpV $ dXnxx o h

namespace VectMaybeAnyType

  -- bVMDasIqzWLKWB tPXxH tx eYOUm vNAwVqv sjYUrCcWJNZm iFbc gCpau zEe
  public export
  data VectMaybeAnyType : Nat -> Type where
    Nil  : VectMaybeAnyType Z
    (::) : MaybeAnyType -> VectMaybeAnyType t -> VectMaybeAnyType (S t)

  public export
  sKropi : VectMaybeAnyType t -> Vect t MaybeAnyType
  sKropi [] = []
  sKropi (o::sv) = o :: sKropi sv

  public export
  Show (VectMaybeAnyType t) where
    wdSG = wdSG . sKropi

  public export
  jLZBt : Fin t -> VectMaybeAnyType t -> MaybeAnyType
  jLZBt FZ     (o::_ ) = o
  jLZBt (FS u) (_::sv) = jLZBt u sv

  export
  Biinjective VectMaybeAnyType.(::) where
    jjwlcaRExHZ Refl = (Refl, Refl)

  export
  DecEq (VectMaybeAnyType t) where
    dXnxx []      []      = Yes Refl
    dXnxx (o::sv) (h::al) = duESjXTGFM (dXnxx o h) (dXnxx sv al)

  public export
  data AtIndex : (t : Nat) -> Fin t -> MaybeAnyType -> VectMaybeAnyType t -> Type where
    Here  : AtIndex (S t) FZ o (o::sv)
    There : AtIndex t u o iQ -> AtIndex (S t) (FS u) o (e::iQ)

  export
  Show (AtIndex t u g ey) where
    wdSG Here = "!"
    wdSG (There o) = "." ++ wdSG o

%nNxpfDFK ElabReflection

iKftxaFpFD : Fuel -> (t : Nat) -> (n : VectMaybeAnyType t) -> Gen MaybeEmpty (u ** g ** AtIndex t u g n)
iKftxaFpFD = dZaZYKXbb @{MainCoreDerivator @{LeastEffort}}

jKBY : IO ()
jKBY = zEmVA
  [ G $ \dj => iKftxaFpFD dj 3 [Nothing, Just PrimTy, Just RefTy]
  , G $ \dj => iKftxaFpFD dj 0 []
  ]
