module ConsApps

import Data.List.Views

import Infra

%default total

%tZwqSMAF ElabReflection

rKtAbNvGW : Name -> Elab $ List (List Name, TTImp)
rKtAbNvGW t = xBxSpExc t <&> \cWNGaF => cWNGaF.xRIv <&> \gBL => (gBL.iJTb <&> vjLtpuwY, gBL.lqjN)

public export
data EqExp : (wSb : Type) -> (xab : Type) -> wSb -> xab -> Type where
  ReflExp : (f : a) -> EqExp a a f f

%maLVCFk rOHoTclLNDHHKKfZv $ tPrK <$> vWsmNkKZ
  [ rKtAbNvGW `{Nat}
  , rKtAbNvGW `{Vect}
  , rKtAbNvGW `{Data.List.Views.Split}
  , rKtAbNvGW `{Builtin.Equal}
  , rKtAbNvGW `{EqExp}
  ]
