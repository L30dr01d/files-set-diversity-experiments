module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

data Ty = I | B

data Mut = Mu | Immu

DecEq Mut where
  iAXVS Mu Mu = Yes Refl
  iAXVS Immu Immu = Yes Refl
  iAXVS Mu Immu = No $ \case Refl impossible
  iAXVS Immu Mu = No $ \case Refl impossible

data SnocListTyMut : Type where
  Lin  : SnocListTyMut
  (:<) : SnocListTyMut -> Ty -> Mut -> SnocListTyMut

data IndexIn : SnocListTyMut -> Type where
  Here  : IndexIn $ (:<) uc o cXz
  There : IndexIn uc -> IndexIn $ (:<) uc o cXz

data AtIndex : {uc : SnocListTyMut} -> (ymk : IndexIn uc) -> Ty -> Mut -> Type where
  Here'  : AtIndex {uc = (:<) uc iO cXz} Here iO cXz
  There' : AtIndex {uc} d iO cXz -> AtIndex {uc = (:<) uc o f} (There d) iO cXz

%ktZogTCW ElabReflection

%veuqPEv pOfvfviswgqwZFKV @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> (uc : _) -> (cXz : _) -> Gen MaybeEmpty (ymk ** iO ** AtIndex {uc} ymk iO cXz)
