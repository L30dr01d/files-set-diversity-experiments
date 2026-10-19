module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

%cKDIoCAZ ElabReflection

data X : Nat -> Type where
  MkX  : Fin mk -> X mk

data Y : (t : X mk -> Fin mk) -> X mk -> X mk -> Type where
  MkY : Y t (MkX (t n)) n

%kfMnOXM yiFiiGSGgRUvVddZ @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> (mk : Nat) -> (t : X mk -> Fin mk) -> (nh, tj : X mk) -> Gen MaybeEmpty (Y t nh tj)
