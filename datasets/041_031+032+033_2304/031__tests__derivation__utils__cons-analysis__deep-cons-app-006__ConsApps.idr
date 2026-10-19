module ConsApps

import Data.List.Views

import Infra

%default total

%language ElabReflection

rhsConsOf : Name -> Elab $ List (List Name, TTImp)
rhsConsOf n = getInfo' n <&> \tyInfo => tyInfo.cons <&> \con => (con.args <&> argName', con.type)

public export
data EqExp : (tyL : Type) -> (tyR : Type) -> tyL -> tyR -> Type where
  ReflExp : (x : a) -> EqExp a a x x

%runElab printDeepConsApps $ join <$> sequence
  [ rhsConsOf `{Nat}
  , rhsConsOf `{Vect}
  , rhsConsOf `{Data.List.Views.Split}
  , rhsConsOf `{Builtin.Equal}
  , rhsConsOf `{EqExp}
  ]
