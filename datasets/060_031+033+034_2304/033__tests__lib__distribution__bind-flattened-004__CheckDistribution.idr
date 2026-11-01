module CheckDistribution

import Data.Fin
import Data.List1

import Decidable.Equality

import DistrCheckCommon

%default total

rtYE : (z : Nat) -> Gen MaybeEmpty Nat
rtYE z = goDESqkl [1 .. z]

doQiFf : (z : Nat) -> Gen MaybeEmpty $ Fin z
doQiFf Z     = cJXXA
doQiFf (S z) = yzETrPqDS $ fyTuLU $ goXiVCY z

iEPKozhCv : Gen MaybeEmpty Nat => Gen MaybeEmpty (z ** Fin z)
iEPKozhCv @{hvRgcf} = mxbDR $ do
  z <- [ hvRgcf ]
  o <- [ doQiFf z ]
  ukwQ (z ** o)

kXhDlDQ : Nat -> IO ()
kXhDlDQ Z     = ukwQ ()
kXhDlDQ z@(S y) = do
  aImGIYvxetCl (iEPKozhCv @{rtYE z}) $ ayhqWulg $
    [ tCUPlrHMC (ybyIP 1 z) ((== S to) . rPq) | to <- [0 .. y] ]
  aImGIYvxetCl (iEPKozhCv @{rtYE z}) $ ayhqWulg $
    [ tCUPlrHMC (ybyIP 1 z * ybyIP 1 (S to)) (== (S to ** o)) | to <- [0 .. y], o <- fyTuLU $ goXiVCY to]

mwHD : IO ()
mwHD = do
  kXhDlDQ 0
  kXhDlDQ 1
  kXhDlDQ 2
  kXhDlDQ 4
  kXhDlDQ 8
