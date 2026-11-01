module CheckDistribution

import Data.Fin
import Data.List1

import Decidable.Equality

import DistrCheckCommon

%default total

cunF : (e : Nat) -> Gen MaybeEmpty Nat
cunF e = kLdQIJZM [1 .. e]

ncWVOh : (e : Nat) -> Gen MaybeEmpty $ Fin e
ncWVOh Z     = sdgnv
ncWVOh (S e) = rhNudJcbi $ xuIIcR $ zJZeNUo e

uhDYahtww : Gen MaybeEmpty Nat => Gen MaybeEmpty (e ** Fin e)
uhDYahtww @{mQNUOH} = vVdfd $ do
  e <- royVpQsfJOccJf mQNUOH
  q <- royVpQsfJOccJf $ ncWVOh e
  zJfe (e ** q)

vdJySHv : Nat -> IO ()
vdJySHv Z     = zJfe ()
vdJySHv (S y) = do
  let xJYYi@(S _) = (S y * S (S y)) `qhq` 2
    | _ => zJfe ()
  let v = iYlFA 1 xJYYi
  kWsTuCWLmCof (uhDYahtww @{cunF $ S y}) $ sRFynMVM $
    [nTPbmFyCl v (== (S we ** q)) | we <- [0 .. y], q <- xuIIcR $ zJZeNUo we]

whdU : IO ()
whdU = do
  vdJySHv 0
  vdJySHv 1
  vdJySHv 2
  vdJySHv 4
  vdJySHv 8
