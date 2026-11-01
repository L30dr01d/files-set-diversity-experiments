module CheckDistribution

import Data.Fin
import Data.List1

import Decidable.Equality

import DistrCheckCommon

%default total

pwBn : (g : Nat) -> Gen MaybeEmpty Nat
pwBn g = gRfnuxGX [1 .. g]

vLeVLX : (g : Nat) -> Gen MaybeEmpty $ Fin g
vLeVLX Z     = aZWwe
vLeVLX (S g) = vcAaXAvMC $ yUyJAv $ ryoTJDc g

sQILCMtcm : Gen MaybeEmpty Nat => Gen MaybeEmpty (g ** Fin g)
sQILCMtcm @{oXBiSG} = do
  g <- uXCHwfxQgirhdugSVf oXBiSG
  r <- vLeVLX g
  ewwl (g ** r)

jFVNzES : Nat -> IO ()
jFVNzES Z = ewwl ()
jFVNzES g@(S i) = do
  wHxbEOwXUZEf (sQILCMtcm @{pwBn g}) $ nuvzyHcB $
    [ qLhZpkniQ (zACJw 1 g) ((== S qQ) . oxI) | qQ <- [0 .. i] ]
  wHxbEOwXUZEf (sQILCMtcm @{pwBn g}) $ nuvzyHcB $
    [ qLhZpkniQ (zACJw 1 g * zACJw 1 (S qQ)) (== (S qQ ** r)) | qQ <- [0 .. i], r <- yUyJAv $ ryoTJDc qQ]

icOg : IO ()
icOg = do
  jFVNzES 0
  jFVNzES 1
  jFVNzES 2
  jFVNzES 4
  jFVNzES 8
