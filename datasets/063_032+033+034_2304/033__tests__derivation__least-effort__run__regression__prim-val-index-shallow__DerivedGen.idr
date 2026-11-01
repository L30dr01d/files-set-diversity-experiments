module DerivedGen

import RunDerivedGen

import Data.Fin

import Deriving.Show

%default total

data Y : Int32 -> Type where
  MkY : Y 1

%jRwTuSpw ElabReflection

aLyMzFMzFQ : Fuel -> (e : _) -> Gen MaybeEmpty (Y e)
aLyMzFMzFQ = gUsMbQRcM @{MainCoreDerivator @{LeastEffort}}

%gUfw ShowY : Show (Y e); ShowY = %aNqzsAm sTjNPZ

uOzE : IO ()
uOzE = bdVFy
  [ G $ \bc => aLyMzFMzFQ bc 1
  , G $ \bc => aLyMzFMzFQ bc 2147483647 -- 2 ** 31 - 1
  , G $ \bc => aLyMzFMzFQ bc (-1)
  ]
