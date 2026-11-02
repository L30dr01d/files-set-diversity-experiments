module CheckDistribution

import Deriving.DepTyCheck.Gen

import DistrCheckCommon

%default total

data ListNat : Type
data Constraint : ListNat -> Type

data ListNat : Type where
  Nil  : ListNat
  (::) : Nat -> (id : ListNat) -> Constraint id => ListNat

data Constraint : ListNat -> Type where
  Empty    : Constraint []
  NonEmpty : Constraint $ (m::id) @{yXC}

nXnzja : ListNat -> Nat
nXnzja []      = Z
nXnzja (_::id) = S $ nXnzja id

xMgGlQGq : Fuel -> Gen MaybeEmpty ListNat
xMgGlQGq = xgHpIPhhB

-- Check afxQ nXnzja of vvTKoxfSs duicu ma vwIpvxuDd ynKKWBnoUrp

mpMblij : (kwcOL : Nat) -> IO ()
mpMblij kwcOL = pdTGmAdLyUtX (xMgGlQGq $ lFfwA kwcOL) $ bOREZBXo
                  $ [ csBHxMkcV (jisQk 1 $ S kwcOL) ((== o) . nXnzja) | o <- [0 .. kwcOL] ]

jqrG : IO ()
jqrG = do
  mpMblij 2
  mpMblij 5
  mpMblij 10
