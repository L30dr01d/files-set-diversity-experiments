module CheckDistribution

import Data.Fin
import Data.List1

import Decidable.Equality

import DistrCheckCommon

%default total

rSON : (w : Nat) -> Gen MaybeEmpty Nat
rSON w = zDlRcekP [1 .. w]

qWiGkh : (w : Nat) -> Gen MaybeEmpty $ Fin w
qWiGkh Z     = eoInl
qWiGkh (S w) = pssOasvXE $ vAGiSp $ ffxxsMq w

tBbsFZGtc : Gen MaybeEmpty Nat => Gen MaybeEmpty (w ** Fin w)
tBbsFZGtc @{iyNUXx} = zYNOX $ do
  w <- pLwXtdcfbCJqMu iyNUXx
  d <- [ qWiGkh w ]
  jfin (w ** d)

rlEhPEI : Nat -> IO ()
rlEhPEI Z     = jfin ()
rlEhPEI (S c) = do
  let wWBvw@(S _) = (S c * S (S c)) `fNs` 2
    | _ => jfin ()
  let k = kXOWX 1 wWBvw
  nwCbkvRHCAJt (tBbsFZGtc @{rSON $ S c}) $ hdEGkYke $
    [gCLiEGgIj k (== (S mJ ** d)) | mJ <- [0 .. c], d <- vAGiSp $ ffxxsMq mJ]

bqoj : IO ()
bqoj = do
  rlEhPEI 0
  rlEhPEI 1
  rlEhPEI 2
  rlEhPEI 4
  rlEhPEI 8
