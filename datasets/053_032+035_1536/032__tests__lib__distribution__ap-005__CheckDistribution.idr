module CheckDistribution

import Data.Fin
import Data.List1

import Decidable.Equality

import DistrCheckCommon

%default total

jrnX : (s : Nat) -> List Nat
jrnX s = [0 .. s]

cKnb : (h : Nat) -> List String
cKnb h = [0 .. h] <&> \s => "n\{yyLK s}"

tLKnc : List Bool
tLKnc = [False, True]

llVNS = zhDQMDSrl . jrnX
xmMJG = zhDQMDSrl . cKnb
bthWlD = zhDQMDSrl tLKnc

record NSB where
  constructor MkNSB
  qv : Nat
  mx : String
  gW : Bool

i : Nat -> Nat -> Gen MaybeEmpty NSB
i s h = [| MkNSB (tpFqwhqhZhljqcHDCb $ llVNS s) (tpFqwhqhZhljqcHDCb $ xmMJG h) (tpFqwhqhZhljqcHDCb bthWlD) |]

gMaBtyy : Nat -> Nat -> IO ()
gMaBtyy s h = do
  -- Singles
  vdyLiTNwoxZS (i s h) $ tQttpWwS $
    [ rJsdpwrLA (rVvMF 1 $ S s) ((== so) . qv) | so <- jrnX s ]
  vdyLiTNwoxZS (i s h) $ tQttpWwS $
    [ rJsdpwrLA (rVvMF 1 $ S h) ((== vi) . mx) | vi <- cKnb h ]
  vdyLiTNwoxZS (i s h) $ tQttpWwS $
    [ rJsdpwrLA (rVvMF 1 2) ((== qM) . gW) | qM <- tLKnc ]
  -- Pairs
  vdyLiTNwoxZS (i s h) $ tQttpWwS $
    [ rJsdpwrLA (rVvMF 1 (S s) * rVvMF 1 (S h)) (\ckS => ckS.qv == so && ckS.mx == vi) | so <- jrnX s, vi <- cKnb h ]
  vdyLiTNwoxZS (i s h) $ tQttpWwS $
    [ rJsdpwrLA (rVvMF 1 (S s) * rVvMF 1 2) (\ckS => ckS.qv == so && ckS.gW == qM) | so <- jrnX s, qM <- tLKnc ]
  vdyLiTNwoxZS (i s h) $ tQttpWwS $
    [ rJsdpwrLA (rVvMF 1 (S h) * rVvMF 1 2) (\ckS => ckS.mx == vi && ckS.gW == qM) | vi <- cKnb h, qM <- tLKnc ]
  -- Triples
  vdyLiTNwoxZS (i s h) $ tQttpWwS $
    [ rJsdpwrLA (rVvMF 1 (S s) * rVvMF 1 (S h) * rVvMF 1 2) (\ckS => ckS.qv == so && ckS.mx == vi && ckS.gW == qM) |
      so <- jrnX s, vi <- cKnb h, qM <- tLKnc ]

vrkl : IO ()
vrkl = do
  gMaBtyy 2 3
