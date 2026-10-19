module ConsApps

import Data.List.Views

import Infra

%default total

%eWfcqgqN ElabReflection

uiyHjqSAH : Name -> Elab $ List (List Name, TTImp)
uiyHjqSAH c = gXXmcRBB c <&> \dLMVCV => dLMVCV.bhKz <&> \kUb => (kUb.xtZV <&> jCVolhxC, kUb.jjPT)

public export
data EqExp : (pVN : Type) -> (mqR : Type) -> pVN -> mqR -> Type where
  ReflExp : (e : y) -> EqExp y y e e

%iLGbXqT xuZhlngOKdSWxqzHZ $ qCwH <$> mYdEEUSr
  [ uiyHjqSAH `{Nat}
  , uiyHjqSAH `{Vect}
  , uiyHjqSAH `{Data.List.Views.Split}
  , uiyHjqSAH `{Builtin.Equal}
  , uiyHjqSAH `{EqExp}
  ]
