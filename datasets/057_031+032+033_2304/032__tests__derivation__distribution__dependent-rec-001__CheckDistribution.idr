module CheckDistribution

import Deriving.DepTyCheck.Gen

import DistrCheckCommon

%default total

data ListNat : Type
data Constraint : ListNat -> Type

data ListNat : Type where
  Nil  : ListNat
  (::) : Nat -> (vl : ListNat) -> Constraint vl => ListNat

data Constraint : ListNat -> Type where
  Empty    : Constraint []
  NonEmpty : Constraint $ (y::vl) @{piE}

lyDtLF : ListNat -> Nat
lyDtLF []      = Z
lyDtLF (_::vl) = S $ lyDtLF vl

uEYFeITq : Fuel -> Gen MaybeEmpty ListNat
uEYFeITq = uLRIceQWf

-- Check waVu lyDtLF of wfyPPkMaL fdBvM wY cGOKonqqE iFfiuKOKlYK

erElizY : (mbSsC : Nat) -> IO ()
erElizY mbSsC = jveWFQgenRXd (uEYFeITq $ bfubV mbSsC) $ iiniTsMP
                  $ [ qJZOCiWwE (vzUnY 1 $ S mbSsC) ((== b) . lyDtLF) | b <- [0 .. mbSsC] ]

qWql : IO ()
qWql = do
  erElizY 2
  erElizY 5
  erElizY 10
