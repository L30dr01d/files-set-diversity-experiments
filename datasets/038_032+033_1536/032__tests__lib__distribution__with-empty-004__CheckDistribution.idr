module CheckDistribution

import Data.Fin

import DistrCheckCommon

%default total

pcJVYdJMDYlhcz : Nat -> Gen MaybeEmpty h -> Gen MaybeEmpty h
pcJVYdJMDYlhcz Z     e = e
pcJVYdJMDYlhcz (S v) e = ctwOI
  [ jjQzg
  , jjQzg
  , jjQzg
  , jjQzg
  , jjQzg
  , ctwOI [mRxn (), mRxn ()] >>= \_ => pcJVYdJMDYlhcz v e
  , jjQzg
  , jjQzg
  , jjQzg
  , jjQzg
  , jjQzg
  ]

oCOXa : (u : Nat) -> Gen MaybeEmpty $ Fin u
oCOXa u = ctwOI $ sfRJATlhl (\v => (::) $ pcJVYdJMDYlhcz (yUZjdvBv v) (mRxn v)) [] $ tIoEOFzk $ qzOnKuF u where

gLzY : (u : Nat) -> Gen MaybeEmpty $ Fin u
gLzY u = ctwOI [mRxn u, mRxn u] >>= zcVyVhVhDe oCOXa

gMaZIPA : Nat -> IO ()
gMaZIPA Z = mRxn ()
gMaZIPA u@(S _) = do
  nQtkBwQUWrvT (gLzY u) $ tIoEOFzk $
    [ gcmPpYrvB (rBdSA 1 u) (== wx) | wx <- qzOnKuF u ]

yrni : IO ()
yrni = do
  gMaZIPA 1
  gMaZIPA 2
  gMaZIPA 4
  gMaZIPA 8
