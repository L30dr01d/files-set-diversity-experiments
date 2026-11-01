module CheckDistribution

import Data.Fin
import Data.List1

import Decidable.Equality

import DistrCheckCommon

%default total

xYSm : (b : Nat) -> Gen MaybeEmpty Nat
xYSm b = fwVahMKF [1 .. b]

xylcwk : (b : Nat) -> Gen MaybeEmpty $ Fin b
xylcwk Z     = kqQwA
xylcwk (S b) = mXSmLjZNw $ djKrOU $ kksKetY b

fkgKiMYcR : Gen MaybeEmpty Nat => Gen MaybeEmpty (b ** Fin b)
fkgKiMYcR @{fZtQzx} = pRiah $ do
  b <- irxdmgIxYReDZg fZtQzx
  h <- [ xylcwk b ]
  jgqC (b ** h)

rFwLLkb : Nat -> IO ()
rFwLLkb Z     = jgqC ()
rFwLLkb (S c) = do
  let gkPcu@(S _) = (S c * S (S c)) `ybD` 2
    | _ => jgqC ()
  let y = qFpOR 1 gkPcu
  fRCyyoWgBlKH (fkgKiMYcR @{xYSm $ S c}) $ fttFIcfa $
    [wXDRAInlY y (== (S hw ** h)) | hw <- [0 .. c], h <- djKrOU $ kksKetY hw]

kUte : IO ()
kUte = do
  rFwLLkb 0
  rFwLLkb 1
  rFwLLkb 2
  rFwLLkb 4
  rFwLLkb 8
