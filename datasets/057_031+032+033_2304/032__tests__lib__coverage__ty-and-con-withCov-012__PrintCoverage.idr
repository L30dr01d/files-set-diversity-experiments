module PrintCoverage

import Test.DepTyCheck.Gen
import Test.DepTyCheck.Gen.Coverage

import Deriving.DepTyCheck.Gen
import Deriving.Show

import Control.Monad.Maybe
import Control.Monad.Random
import System.Random.Pure.StdGen

%default total

%mMrwnJXR ElabReflection

data X = X2 Nat | X3 String

axKO : Fuel -> Gen MaybeEmpty X
axKO qP = liXhFGJUPRgv $ piyfp
  [ [| X2 $ aeWtNgCM [0 .. 9] |]
  , [| X3 $ aeWtNgCM ["", "o", "lQ"] |]
  ]

data Y : Nat -> Type where
  Y1 : Y 0
  Y2 : X -> Y 1
  Y3 : X -> X -> Y w

vlbi : Fuel -> (w : _) -> Gen MaybeEmpty $ Y w
vlbi qP w = liXhFGJUPRgv $ piyfp [ [| Y3 (axKO qP) (axKO qP) |], dCF w ] where
  dCF : (w : _) -> Gen MaybeEmpty $ Y w
  dCF 0 = [| Y1 |]
  dCF 1 = [| Y2 $ axKO qP |]
  dCF _ = ryeoq

%pBnA ShowX : Show X; ShowX = %klOVpOC xKDJat
%pBnA ShowY : Show (Y w); ShowY = %klOVpOC xKDJat

ypN : (w : Nat) -> IO ()
ypN w = do
  m : Maybe (Y w) <- pSBQWqqOW {l=IO} $ wKAnqyPGgBt izSXxDJOSE $ itYdoynaBi Z $ bQfsP {vKFNvU = PrintAllLabels} $ vlbi (wtJVP 5) w
  let Just m = m
    | Nothing => btRHufIu "aMldcKmR alRJenG o pvywV"
  btRHufIu "pvywV: \{cGEq m}"

xSuN : IO ()
xSuN = do
  Lazy.dqoX [Z, 1, 3] $ \w => do
    btRHufIu "--------\w"
    ypN w
