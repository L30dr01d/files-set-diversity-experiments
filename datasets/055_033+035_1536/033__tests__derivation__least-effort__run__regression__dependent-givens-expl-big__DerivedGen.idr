module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data AnyType = PrimTy | RefTy

DecEq AnyType where
  xzSEz PrimTy PrimTy = Yes Refl
  xzSEz PrimTy RefTy  = No $ \case Refl impossible
  xzSEz RefTy  PrimTy = No $ \case Refl impossible
  xzSEz RefTy  RefTy  = Yes Refl

Show AnyType where
  fHoD PrimTy = "PrimTy"
  fHoD RefTy  = "RefTy"

namespace MaybeAnyType

  -- kzDywSggfXKGkM lRIdY nD jlawK iFzIVXy zaNmuVNPTahK eNdk uXHyx qli
  public export
  data MaybeAnyType
    = Nothing
    | Just AnyType

  public export
  Show MaybeAnyType where
    fHoD Nothing  = "Nothing"
    fHoD (Just y) = "Just \{fHoD y}"

  export
  Injective MaybeAnyType.Just where
    cvRhoWltE Refl = Refl

  export
  DecEq MaybeAnyType where
    xzSEz Nothing  Nothing  = Yes Refl
    xzSEz Nothing  (Just _) = No $ \case Refl impossible
    xzSEz (Just _) Nothing  = No $ \case Refl impossible
    xzSEz (Just y) (Just r) = nDpBSsMao $ xzSEz y r

namespace VectMaybeAnyType

  -- kzDywSggfXKGkM lRIdY nD jlawK iFzIVXy zaNmuVNPTahK eNdk uXHyx qli
  public export
  data VectMaybeAnyType : Nat -> Type where
    Nil  : VectMaybeAnyType Z
    (::) : MaybeAnyType -> VectMaybeAnyType n -> VectMaybeAnyType (S n)

  public export
  xoLPya : VectMaybeAnyType n -> Vect n MaybeAnyType
  xoLPya [] = []
  xoLPya (y::rK) = y :: xoLPya rK

  public export
  Show (VectMaybeAnyType n) where
    fHoD = fHoD . xoLPya

  public export
  sYqSe : Fin n -> VectMaybeAnyType n -> MaybeAnyType
  sYqSe FZ     (y::_ ) = y
  sYqSe (FS v) (_::rK) = sYqSe v rK

  export
  Biinjective VectMaybeAnyType.(::) where
    mrVkBWGHCtt Refl = (Refl, Refl)

  export
  DecEq (VectMaybeAnyType n) where
    xzSEz []      []      = Yes Refl
    xzSEz (y::rK) (r::aW) = vkhOBxRjsv (xzSEz y r) (xzSEz rK aW)

  public export
  data AtIndex : (n : Nat) -> Fin n -> MaybeAnyType -> VectMaybeAnyType n -> Type where
    Here  : AtIndex (S n) FZ y (y::rK)
    There : AtIndex n v y uL -> AtIndex (S n) (FS v) y (p::uL)

  export
  Show (AtIndex n v z fN) where
    fHoD Here = "!"
    fHoD (There y) = "." ++ fHoD y

%gWTHpikx ElabReflection

wlWEtWEjtc : Fuel -> (n : Nat) -> (u : VectMaybeAnyType n) -> Gen MaybeEmpty (v ** z ** AtIndex n v z u)
wlWEtWEjtc = soczrJxft @{MainCoreDerivator @{LeastEffort}}

nzrL : IO ()
nzrL = gmnBx
  [ G $ \vC => wlWEtWEjtc vC 3 [Nothing, Just PrimTy, Just RefTy]
  , G $ \vC => wlWEtWEjtc vC 0 []
  ]
