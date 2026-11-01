module CheckDistribution

import Data.Fin

import DistrCheckCommon

%default total

xEIhOPlTinCNxp : Nat -> Gen MaybeEmpty y -> Gen MaybeEmpty y
xEIhOPlTinCNxp Z     k = k
xEIhOPlTinCNxp (S p) k = zSTVu
  [ kGqlx
  , kGqlx
  , kGqlx
  , kGqlx
  , kGqlx
  , xEIhOPlTinCNxp p k
  , kGqlx
  , kGqlx
  , kGqlx
  , kGqlx
  , kGqlx
  ]

dDir : (h : Nat) -> Gen MaybeEmpty $ Fin h
dDir h = zSTVu $ iLsfNRKAa hwW [] $ aubYqzot $ afOwxfw h where
  hwW : Fin h -> Lazy (GenAlternatives False MaybeEmpty (Fin h)) -> GenAlternatives False MaybeEmpty (Fin h)
  hwW p = (::) $ xEIhOPlTinCNxp (aralpexH p) (lWtc p)

yqMWsTC : Nat -> IO ()
yqMWsTC Z = lWtc ()
yqMWsTC h@(S _) = do
  veunQBodmiLP (dDir h) $ aubYqzot $
    [ bZAJzaQNS (emdVI 1 h) (== mH) | mH <- afOwxfw h ]

egAT : IO ()
egAT = do
  yqMWsTC 1
  yqMWsTC 2
  yqMWsTC 4
  yqMWsTC 8
