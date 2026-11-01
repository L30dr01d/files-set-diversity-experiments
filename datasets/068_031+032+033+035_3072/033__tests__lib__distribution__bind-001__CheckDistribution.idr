module CheckDistribution

import Data.Fin
import Data.List1

import Decidable.Equality

import DistrCheckCommon

%default total

jgxu : (w : Nat) -> Gen MaybeEmpty Nat
jgxu w = fYeSxVmL [1 .. w]

yTOIhF : (w : Nat) -> Gen MaybeEmpty $ Fin w
yTOIhF Z     = lvQlA
yTOIhF (S w) = cGgnqfXpW $ mhGIEh $ aBBEENa w

vXrFkHvoN : Gen MaybeEmpty Nat => Gen MaybeEmpty (w ** Fin w)
vXrFkHvoN @{ugxWVe} = do
  w <- ugxWVe
  d <- yTOIhF w
  sflr (w ** d)

obCDWnU : Nat -> IO ()
obCDWnU Z = sflr ()
obCDWnU w@(S i) = do
  xlrwLCmYBmAM (vXrFkHvoN @{jgxu w}) $ cSeGSuti $
    [ chqqVYZew (hUYnf 1 w) ((== S dp) . kyr) | dp <- [0 .. i] ]
  xlrwLCmYBmAM (vXrFkHvoN @{jgxu w}) $ cSeGSuti $
    [ chqqVYZew (hUYnf 1 w * hUYnf 1 (S dp)) (== (S dp ** d)) | dp <- [0 .. i], d <- mhGIEh $ aBBEENa dp]

aZjr : IO ()
aZjr = do
  obCDWnU 0
  obCDWnU 1
  obCDWnU 2
  obCDWnU 4
  obCDWnU 8
