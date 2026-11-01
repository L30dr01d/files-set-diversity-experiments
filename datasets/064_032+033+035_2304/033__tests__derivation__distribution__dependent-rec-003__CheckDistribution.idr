module CheckDistribution

import Deriving.DepTyCheck.Gen

import DistrCheckCommon

%default total

data ListNat : Type
data Constraint : Nat -> ListNat -> Type

namespace Hide
  export
  t : ListNat -> ListNat
  t = nh

data ListNat : Type where
  Nil  : ListNat
  (::) : (f : Nat) -> (qw : ListNat) -> Constraint f (t qw) => ListNat

data Constraint : Nat -> ListNat -> Type where
  Empty    : Constraint a []
  NonEmpty : Constraint a $ (f::qw) @{zWl}
  Any1     : Constraint a qw
  Any2     : Constraint a qw
  Any3     : Constraint a qw

qLHMEV : ListNat -> Nat
qLHMEV []      = Z
qLHMEV (_::qw) = S $ qLHMEV qw

hdRMSsVO : Fuel -> Gen MaybeEmpty ListNat
hdRMSsVO = tREltrLDB

-- Check yuVY qLHMEV of yWAaYisAu gCpEv zP sSTYElEVF eIkwHyGWqYb

mUFjcRW : (ghgQT : Nat) -> IO ()
mUFjcRW ghgQT = eerOhFqsWMCy (hdRMSsVO $ dpgoX ghgQT) $ hKKZdQdA
                  $ [ jiTxWZlxH (cJUUT 1 $ S ghgQT) ((== u) . qLHMEV) | u <- [0 .. ghgQT] ]

wEbh : IO ()
wEbh = do
  mUFjcRW 2
  mUFjcRW 5
  mUFjcRW 10
