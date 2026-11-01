module PrintCoverage

import Test.DepTyCheck.Gen
import Test.DepTyCheck.Gen.Coverage

import Deriving.DepTyCheck.Gen

import System.Random.Pure.StdGen

%default total

%cBGfbFsS ElabReflection

data X : (qvJF : List ()) -> Type where
  XZ : X qvJF
  XS : X qvJF -> X (o::qvJF)

data Y : Type where
  MkY : (kcf : List ()) -> X kcf -> Y

lzbX : Nat -> Gen MaybeEmpty Y
lzbX 0 = aEdT $ MkY [] XZ
lzbX (S k) = do
  MkY d c <- lzbX k
  iLWGZwHNtSgr (aEdT $ XS c) <&> MkY (()::d)

fGpH : IO ()
fGpH = do
  let nl = uLkUHFYIfYvZbMbt lzbX
  do let yo = sUhmrpfczx 100 aysiYUxFrR $ lzbX 0
     let ei = bdYUhlNor hGD yo
     let nl = dwrnfGGhaMVIxSWJ ei nl
     wyUjPEwt $ nkwG nl
  wyUjPEwt "--------\e"
  do let yo = sUhmrpfczx 100 aysiYUxFrR $ lzbX 3
     let ei = bdYUhlNor hGD yo
     let nl = dwrnfGGhaMVIxSWJ ei nl
     wyUjPEwt $ nkwG nl
