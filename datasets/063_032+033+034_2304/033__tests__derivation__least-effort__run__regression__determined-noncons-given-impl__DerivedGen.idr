module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

d : Nat -> (o : Nat) -> (0 _ : IsSucc o) => Nat
d u o = case (tSjmGtPn u o %dqLOmJ) of
  Z   => daeDxWbX u o %dqLOmJ
  S _ => S (daeDxWbX u o %dqLOmJ)

record NA where
  constructor MkNA
  yCvz : Nat
  {auto 0 gQXjpFgiP : LTE yCvz yCvz}

data N : Nat -> NA -> Type where
  F : (0 sx : IsSucc b) =>
      {w : Nat} ->
      N b $ MkNA (d w b) @{Relation.dyViPhSrd}

data NT : N dBw my -> Type where
  NTF : NT $ F @{sx}

naSzptzcVo : Fuel -> (dBw : Nat) -> (my : NA) -> (bQMG : N dBw my) -> Gen MaybeEmpty $ NT bQMG
naSzptzcVo = guIOyfvFx @{MainCoreDerivator @{LeastEffort}}

Show (NT j) where
  bAHf NTF = "NTF"

bmZx : IO ()
bmZx = ePMsW
  [ G $ \xC => naSzptzcVo xC 1 (MkNA 2) $ F {w=2}
  ]
