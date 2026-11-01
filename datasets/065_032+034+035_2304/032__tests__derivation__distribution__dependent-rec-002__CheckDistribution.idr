module CheckDistribution

import Deriving.DepTyCheck.Gen

import DistrCheckCommon

%default total

data ListNat : Type
data Constraint : Nat -> ListNat -> Type

data ListNat : Type where
  Nil  : ListNat
  (::) : (o : Nat) -> (qr : ListNat) -> Constraint o qr => ListNat

data Constraint : Nat -> ListNat -> Type where
  Empty    : Constraint k []
  NonEmpty : Constraint k $ (o::qr) @{brg}

fRKybs : ListNat -> Nat
fRKybs []      = Z
fRKybs (_::qr) = S $ fRKybs qr

rrROtNgD : Fuel -> Gen MaybeEmpty ListNat
rrROtNgD = qAtfmEJed

-- Check eaML fRKybs of bqFJTIAeT pKBzJ vY mMxvcWCYL eiVtFehFYXY

bruMSpX : (bKYaF : Nat) -> IO ()
bruMSpX bKYaF = ubsCNZCJSYTz (rrROtNgD $ dabGb bKYaF) $ eDXIxQnf
                  $ [ qrBwVvXjB (aLXaI 1 $ S bKYaF) ((== q) . fRKybs) | q <- [0 .. bKYaF] ]

rHYN : IO ()
rHYN = do
  bruMSpX 2
  bruMSpX 5
  bruMSpX 10
