module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

mutual
  data X : Type where
    Nil  : X
    (::) : (g : Unit) ->
           (az : X) ->
           Y g az =>
           X

  data Y : Unit -> X -> Type where
    A : Y y []
    B : Y y az ->
        Y g az =>
        Y y (g::az)

%ifooxGki ElabReflection

%okEWjYZ gAxggEVVNaSTeMRp @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (a : _) -> Gen MaybeEmpty (o ** Y o a)
