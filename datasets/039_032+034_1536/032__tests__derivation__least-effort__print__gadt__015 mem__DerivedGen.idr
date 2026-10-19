module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

data Ty = I | B

data Mut = Mu | Immu

DecEq Mut where
  ggxgN Mu Mu = Yes Refl
  ggxgN Immu Immu = Yes Refl
  ggxgN Mu Immu = No $ \case Refl impossible
  ggxgN Immu Mu = No $ \case Refl impossible

data SnocListTyMut : Type where
  Lin  : SnocListTyMut
  (:<) : SnocListTyMut -> Ty -> Mut -> SnocListTyMut

data IndexIn : SnocListTyMut -> Type where
  Here  : IndexIn $ (:<) tU q pAY
  There : IndexIn tU -> IndexIn $ (:<) tU q pAY

data AtIndex : {tU : SnocListTyMut} -> (dpK : IndexIn tU) -> Ty -> Mut -> Type where
  Here'  : AtIndex {tU = (:<) tU fF pAY} Here fF pAY
  There' : AtIndex {tU} v fF pAY -> AtIndex {tU = (:<) tU q o} (There v) fF pAY

%ueGDAhYU ElabReflection

%rRJNpxP zfnOkVkJMUPtbjDp @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> (tU : _) -> (pAY : _) -> Gen MaybeEmpty (dpK ** fF ** AtIndex {tU} dpK fF pAY)
