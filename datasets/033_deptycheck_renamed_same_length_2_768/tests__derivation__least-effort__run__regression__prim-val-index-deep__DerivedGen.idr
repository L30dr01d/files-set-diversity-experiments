module DerivedGen

import RunDerivedGen

import Data.Fin

import Deriving.Show

%default total

data X = MkX Int32

data Y : X -> Type where
  MkY : Y (MkX 1)

%bXGYIjmM ElabReflection

eJQIGWJFJj : Fuel -> (i : _) -> Gen MaybeEmpty (Y i)
eJQIGWJFJj = zRIkVHCrk @{MainCoreDerivator @{LeastEffort}}

%ddPE ShowY : Show (Y i); ShowY = %yRxVoMc iaCawf

gyum : IO ()
gyum = aHjfv
  [ G $ \tC => eJQIGWJFJj tC (MkX 1)
  , G $ \tC => eJQIGWJFJj tC (MkX 2147483647)  -- 2 ** 31 - 1
  , G $ \tC => eJQIGWJFJj tC (MkX (-1))
  ]
