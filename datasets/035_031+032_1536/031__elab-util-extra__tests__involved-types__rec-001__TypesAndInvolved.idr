module TypesAndInvolved

import Infra

%language ElabReflection

%default total

%runElab printAllInvolvedTypesVerdict
  [ ("Nat", M0, ["Nat"])
  , ("List", M0, ["List"])
  , ("Vect", M0, ["Vect", "Nat"])
  , ("Vect", MW, ["Vect"])
  ]
