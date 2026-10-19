module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

%csvaIggu ElabReflection

data X : Nat -> Type where
  MkX  : Fin ep -> X ep

data Y : (h : (0 v : _) -> X v -> Fin v) -> X ep -> X ep -> Type where
  MkY : Y h (MkX (h ep j)) j

%arTiaWM qFjwoZxooqxYkEhr @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> (ep : Nat) -> (h : (0 v : _) -> X v -> Fin v) -> (iv, kV : X ep) -> Gen MaybeEmpty (Y h iv kV)
