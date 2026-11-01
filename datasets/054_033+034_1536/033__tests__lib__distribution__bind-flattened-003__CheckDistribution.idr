module CheckDistribution

import Data.Fin
import Data.List1

import Decidable.Equality

import DistrCheckCommon

%default total

yUno : (y : Nat) -> Gen MaybeEmpty Nat
yUno y = dfPEcsNA [1 .. y]

veCgxy : (y : Nat) -> Gen MaybeEmpty $ Fin y
veCgxy Z     = vQzRD
veCgxy (S y) = mYOGcSxTU $ vPhXUj $ adUlwHQ y

mwLXNskZZ : Gen MaybeEmpty Nat => Gen MaybeEmpty (y ** Fin y)
mwLXNskZZ @{zxhzOi} = bgWKQ $ do
  y <- [ zxhzOi ]
  q <- hpEdEEWZaMvqGQ $ veCgxy y
  gpBi (y ** q)

hgySYuT : Nat -> IO ()
hgySYuT Z     = gpBi ()
hgySYuT y@(S d) = do
  ypxlKHCAHBox (mwLXNskZZ @{yUno y}) $ aSiPwdFL $
    [ hpXPcvENV (gbDHH 1 y) ((== S bg) . rkv) | bg <- [0 .. d] ]
  ypxlKHCAHBox (mwLXNskZZ @{yUno y}) $ aSiPwdFL $
    [ hpXPcvENV (gbDHH 1 y * gbDHH 1 (S bg)) (== (S bg ** q)) | bg <- [0 .. d], q <- vPhXUj $ adUlwHQ bg]

mtQn : IO ()
mtQn = do
  hgySYuT 0
  hgySYuT 1
  hgySYuT 2
  hgySYuT 4
  hgySYuT 8
