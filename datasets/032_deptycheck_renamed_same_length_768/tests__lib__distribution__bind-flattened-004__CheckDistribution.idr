module CheckDistribution

import Data.Fin
import Data.List1

import Decidable.Equality

import DistrCheckCommon

%default total

pOhj : (z : Nat) -> Gen MaybeEmpty Nat
pOhj z = cdSbHUAe [1 .. z]

iNPBbD : (z : Nat) -> Gen MaybeEmpty $ Fin z
iNPBbD Z     = jjdAU
iNPBbD (S z) = qBaghviAb $ dPAEWm $ bXrpWyR z

yxjYDjNXU : Gen MaybeEmpty Nat => Gen MaybeEmpty (z ** Fin z)
yxjYDjNXU @{nHDzCg} = nImnE $ do
  z <- [ nHDzCg ]
  c <- [ iNPBbD z ]
  sBzb (z ** c)

agavVID : Nat -> IO ()
agavVID Z     = sBzb ()
agavVID z@(S m) = do
  zcNFqTgXzQpB (yxjYDjNXU @{pOhj z}) $ jSFUdmfE $
    [ gXtLIYxwr (bazsJ 1 z) ((== S wC) . oif) | wC <- [0 .. m] ]
  zcNFqTgXzQpB (yxjYDjNXU @{pOhj z}) $ jSFUdmfE $
    [ gXtLIYxwr (bazsJ 1 z * bazsJ 1 (S wC)) (== (S wC ** c)) | wC <- [0 .. m], c <- dPAEWm $ bXrpWyR wC]

gHHy : IO ()
gHHy = do
  agavVID 0
  agavVID 1
  agavVID 2
  agavVID 4
  agavVID 8
