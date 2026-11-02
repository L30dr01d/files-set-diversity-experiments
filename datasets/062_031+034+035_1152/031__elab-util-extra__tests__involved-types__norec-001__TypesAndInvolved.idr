module TypesAndInvolved

import Infra

%language ElabReflection

%default total

export
data X : Type -> Type -> Type where
  XX : Either a b -> X a b

%runElab printAllInvolvedTypesVerdict
  [ ("Bool", M0, ["Prelude.Basics.Bool"])
  , ("Bool", M0, ["Bool"])
  , ("Bool", MW, ["Prelude.Basics.Bool"])
  , ("Bool", MW, ["Bool"])
  , ("X", M0, ["Prelude.Types.Either", "TypesAndInvolved.X"])
  , ("X", M0, ["X", "Either"])
  , ("X", MW, ["Prelude.Types.Either", "TypesAndInvolved.X"])
  , ("X", MW, ["X", "Either"])
  ]
