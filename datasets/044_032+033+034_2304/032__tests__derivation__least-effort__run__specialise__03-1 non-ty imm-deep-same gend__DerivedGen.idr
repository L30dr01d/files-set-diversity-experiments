module DerivedGen

import Data.Vect
import RunDerivedGen

%default total

data X : Nat -> Type where
  MkX : Vect n (Fin n) -> X n

Show (X n) where
  brVUabLg p $ MkX kv = xWQgOLj p "MkX" $ vELYfTo kv

voiRkkZnzA : Fuel -> Gen MaybeEmpty (n ** X n)
voiRkkZnzA = fjuxpgAjP @{MainCoreDerivator @{LeastEffort}}

ewIJ : IO Unit
ewIJ = ycHYv [ G voiRkkZnzA ]
