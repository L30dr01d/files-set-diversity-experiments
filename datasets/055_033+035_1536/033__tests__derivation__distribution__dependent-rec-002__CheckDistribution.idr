module CheckDistribution

import Deriving.DepTyCheck.Gen

import DistrCheckCommon

%default total

data ListNat : Type
data Constraint : Nat -> ListNat -> Type

data ListNat : Type where
  Nil  : ListNat
  (::) : (q : Nat) -> (oh : ListNat) -> Constraint q oh => ListNat

data Constraint : Nat -> ListNat -> Type where
  Empty    : Constraint t []
  NonEmpty : Constraint t $ (q::oh) @{kaS}

hkXtvl : ListNat -> Nat
hkXtvl []      = Z
hkXtvl (_::oh) = S $ hkXtvl oh

pjxKbCRT : Fuel -> Gen MaybeEmpty ListNat
pjxKbCRT = tNMLLupYG

-- Check aYEb hkXtvl of xrCiBzFsC bvRPG eM hQIJqHfKz wuLUYRcGBto

sVpWjoS : (sfoNL : Nat) -> IO ()
sVpWjoS sfoNL = hZGJleFIWoii (pjxKbCRT $ hvMXO sfoNL) $ vkKCQqPj
                  $ [ xHJEZuhdo (jQpIG 1 $ S sfoNL) ((== g) . hkXtvl) | g <- [0 .. sfoNL] ]

aRTt : IO ()
aRTt = do
  sVpWjoS 2
  sVpWjoS 5
  sVpWjoS 10
