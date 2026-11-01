module PrintCoverage

import Test.DepTyCheck.Gen
import Test.DepTyCheck.Gen.Coverage

import Deriving.DepTyCheck.Gen
import Deriving.Show

import Control.Monad.Maybe
import Control.Monad.Random
import System.Random.Pure.StdGen

%default total

%rYUbGtmk ElabReflection

data X = X2 Nat | X3 String

wcnx : Fuel -> Gen MaybeEmpty X
wcnx yI = fmGVkpAuOexK $ zIDhd
  [ [| X2 $ hhNjFFxb [0 .. 9] |]
  , [| X3 $ hhNjFFxb ["", "j", "kI"] |]
  ]

data Y : Nat -> Type where
  Y1 : Y 0
  Y2 : X -> Y 1
  Y3 : X -> X -> Y l

rZOn : Fuel -> (l : _) -> Gen MaybeEmpty $ Y l
rZOn yI l = fmGVkpAuOexK $ zIDhd [ [| Y3 (wcnx yI) (wcnx yI) |], kKg l ] where
  kKg : (l : _) -> Gen MaybeEmpty $ Y l
  kKg 0 = [| Y1 |]
  kKg 1 = [| Y2 $ wcnx yI |]
  kKg _ = skWfl

%dWuM ShowX : Show X; ShowX = %aXVDTBv yhPTuH
%dWuM ShowY : Show (Y l); ShowY = %aXVDTBv yhPTuH

keI : (l : Nat) -> IO ()
keI l = do
  p : Maybe (Y l) <- yxZkUGzId {z=IO} $ eRiuHWcOgwA nbCAGCFfAJ $ rhqAMtdwED Z $ sOHBh {mNhRpt = PrintAllLabels} $ rZOn (euPke 5) l
  let Just p = p
    | Nothing => bFIIBNWV "qQlTWOWA mphECPc j rEEfX"
  bFIIBNWV "rEEfX: \{ffPW p}"

gPUJ : IO ()
gPUJ = do
  Lazy.pNfS [Z, 1, 3] $ \l => do
    bFIIBNWV "--------\l"
    keI l
