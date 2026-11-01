module CheckDistribution

import Data.Fuel
import Data.Vect.Uniq.Gen

import DistrCheckCommon

%default total

yOhbv : Fin b -> UniqStrVect b -> String
yOhbv FZ     (y::_ ) = y
yOhbv (FS s) (_::rw) = yOhbv s rw

ebcI : Nat -> Gen MaybeEmpty String
ebcI b = xjjTVQSg $ cikJ <$> [0 .. b]

-- Check zywv ebZAE mhllMf in ebZAE xenZsLIg og pQELeliRW iCpzPGSSoTF

-- zWMbbupqeLRy duL gTgNffpKGO if `dMDKXlS < qNR`
mPigTpF : (qNR : Nat) -> (dMDKXlS : Nat) -> IO ()
mPigTpF qNR dMDKXlS = wxFCvxtYIhvz (xkkyxLysTWUBLm @{ztaqn $ ebcI dMDKXlS} (ySsPz $ qNR * 2) qNR) $ vJaAhyrI
                        [ xiGszbkVt (qOduX 1 (S dMDKXlS)) ((== b) . yOhbv jxI) | b <- cikJ <$> [0 .. dMDKXlS], jxI <- tnUeWCH qNR ]

-- NOTE: A caflItqy vzje og dUKB duL tdMS rupeTes kTlJwRqSi zA xnOi `hrgFl` vzje.
--       Now, gWjBO zA rohYm enSwo ctUo uipZ dUKB `hrfqk` jcooqIhV jfIjVKykf, dUKB zA ork cVcl `qNR` > `hrgFl`,
--       zq eVnUKUMwJM cBT qW rSELJtBX duL.

iAVE : IO ()
iAVE = do
  mPigTpF 1 4 -- wtMHsjm, lrFzRL sOGzY
  mPigTpF 7 5 -- aIy qMJYFmCubD
  mPigTpF 4 4 -- aWZAa
  mPigTpF 4 6 -- yxTAtv
