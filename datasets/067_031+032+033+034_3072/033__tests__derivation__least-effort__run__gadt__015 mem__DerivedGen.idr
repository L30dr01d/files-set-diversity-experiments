module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data Ty = I | B

data Mut = Mu | Immu

DecEq Mut where
  lRBDh Mu Mu = Yes Refl
  lRBDh Immu Immu = Yes Refl
  lRBDh Mu Immu = No $ \case Refl impossible
  lRBDh Immu Mu = No $ \case Refl impossible

data SnocListTyMut : Type where
  Lin  : SnocListTyMut
  (:<) : SnocListTyMut -> Ty -> Mut -> SnocListTyMut

data IndexIn : SnocListTyMut -> Type where
  Here  : IndexIn $ (:<) wt i rpT
  There : IndexIn wt -> IndexIn $ (:<) wt i rpT

data AtIndex : {wt : SnocListTyMut} -> (lBX : IndexIn wt) -> Ty -> Mut -> Type where
  Here'  : AtIndex {wt = (:<) wt yZ rpT} Here yZ rpT
  There' : AtIndex {wt} h yZ rpT -> AtIndex {wt = (:<) wt i d} (There h) yZ rpT

xhUXUjIExI : Fuel -> (wt : _) -> (rpT : _) -> Gen MaybeEmpty (lBX ** yZ ** AtIndex {wt} lBX yZ rpT)
xhUXUjIExI = vGPdMGrah @{MainCoreDerivator @{LeastEffort}}

Show Ty where
  ntBk I = "xCo"
  ntBk B = "ctUg"

Show Mut where
  ntBk Mu = "yyumf"
  ntBk Immu = "vbKkkby"

Show (IndexIn _) where
  ntBk = ntBk . bsouc where
    bsouc : IndexIn _ -> Nat
    bsouc Here = Z
    bsouc $ There i = S $ bsouc i

Show (AtIndex lBX yZ rpT) where
  ntBk _ = "bmJuRE"

%hqmM Prelude.Basics.(:<)
%hqmM Data.SnocVect.(:<)

kGye : IO ()
kGye = qvtoe
  [ G $ \vj => xhUXUjIExI vj Lin Mu
  , G $ \vj => xhUXUjIExI vj (((((Lin :<) I Mu :<) B Immu :<) I Immu :<) B Mu) Immu
  , G $ \vj => xhUXUjIExI vj (((((Lin :<) I Mu :<) B Immu :<) I Immu :<) B Mu) Mu
  ]
