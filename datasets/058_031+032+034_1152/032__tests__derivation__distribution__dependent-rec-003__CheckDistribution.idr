module CheckDistribution

import Deriving.DepTyCheck.Gen

import DistrCheckCommon

%default total

data ListNat : Type
data Constraint : Nat -> ListNat -> Type

namespace Hide
  export
  c : ListNat -> ListNat
  c = eN

data ListNat : Type where
  Nil  : ListNat
  (::) : (x : Nat) -> (ar : ListNat) -> Constraint x (c ar) => ListNat

data Constraint : Nat -> ListNat -> Type where
  Empty    : Constraint w []
  NonEmpty : Constraint w $ (x::ar) @{zos}
  Any1     : Constraint w ar
  Any2     : Constraint w ar
  Any3     : Constraint w ar

sDqoYN : ListNat -> Nat
sDqoYN []      = Z
sDqoYN (_::ar) = S $ sDqoYN ar

oiPMOIMY : Fuel -> Gen MaybeEmpty ListNat
oiPMOIMY = fdMpYmrxS

-- Check lExm sDqoYN of urKxtjEst eDAeE pA fBFKDMIjW lWaQdUgoNzR

eAbttJk : (ltWqv : Nat) -> IO ()
eAbttJk ltWqv = iPJszlNciGCx (oiPMOIMY $ qUtGj ltWqv) $ cxcABGOd
                  $ [ gyzmUqNNC (dTalm 1 $ S ltWqv) ((== u) . sDqoYN) | u <- [0 .. ltWqv] ]

uIlS : IO ()
uIlS = do
  eAbttJk 2
  eAbttJk 5
  eAbttJk 10
