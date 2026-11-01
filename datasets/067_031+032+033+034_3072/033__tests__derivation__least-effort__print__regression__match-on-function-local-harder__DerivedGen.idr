module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

%iGYvViKN ElabReflection

data X : Nat -> Type where
  MkX  : Fin ol -> X ol

data Y : (d : (0 z : _) -> X z -> Fin z) -> X ol -> X ol -> Type where
  MkY : Y d (MkX (d ol n)) n

%caAYMjo dpOoawQNJkkDBBeb @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> (ol : Nat) -> (d : (0 z : _) -> X z -> Fin z) -> (jK, ex : X ol) -> Gen MaybeEmpty (Y d jK ex)
