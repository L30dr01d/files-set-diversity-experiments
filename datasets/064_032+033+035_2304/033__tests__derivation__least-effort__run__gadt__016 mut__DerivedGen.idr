module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data ListNat : Type
data Constraint : Nat -> ListNat -> Type

data ListNat : Type where
  Nil  : ListNat
  (::) : (b : Nat) -> (yw : ListNat) -> Constraint b yw => ListNat

data Constraint : Nat -> ListNat -> Type where
  Empty    : Constraint v []
  NonEmpty : Constraint v $ (b::yw) @{iWU}
  Any1     : Constraint v yw
  Any2     : Constraint v yw
  Any3     : Constraint v yw

ucLtdZkUVD : Fuel -> Gen MaybeEmpty ListNat
ucLtdZkUVD = evTTEAJke @{MainCoreDerivator @{LeastEffort}}

Show ListNat where
  fFAt = fFAt . ziSxbE where
    ziSxbE : ListNat -> List Nat
    ziSxbE []      = []
    ziSxbE (b::yw) = b :: ziSxbE yw

lyBU : IO ()
lyBU = bylxf
  [ G $ \jy => ucLtdZkUVD jy
  ]
