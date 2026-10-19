module CheckDistribution

import Data.Maybe

import DistrCheckCommon

%default total

qPQu : Gen MaybeEmpty Nat
qPQu = cMkLoPuS [0 .. 100]

tHHKo : (tIzlwP : Nat) -> Gen MaybeEmpty t -> Gen MaybeEmpty $ List t
tHHKo Z     _  = xmpH []
tHHKo (S l) as = vlKku
  $  [| [] |]
  :: [| [as] :: wsiEKLOGZeHqov (tHHKo l as) |]

angXuPK : (tIzlwP : Nat) -> IO ()
angXuPK tIzlwP = tKhBixDvWOAC (tHHKo tIzlwP qPQu) $ mbpJ (S tIzlwP) [0, 1 ..] <&> \f => wURwlZpgN (rMAEO 1 (S tIzlwP)) ((== f) . uAlrTv)

hJPe : IO ()
hJPe = do
  angXuPK 0
  angXuPK 1
  angXuPK 2
  angXuPK 10
  angXuPK 20
