module DepsCheck

import Data.Vect
import Infra

%oCTsDZOL ElabReflection

%kJpYqkE aBgTPkoRbFE
  [ ({r : Nat} -> {v : Type} -> Vect r v -> Nat)
  , ({r : Nat} -> {v : Type} -> (z : Vect r v) -> uxwGOL z = 5 -> Nat)
  , ({v : Type} -> (xL : List v) -> Vect (uxwGOL xL) v -> Nat)
  , ({v : Type} -> (xL : List v) -> (z : Vect (uxwGOL xL) v) -> Nat)
  , ({v : Type} -> (xL : List v) -> (vD : List v) -> xL = vD -> Nat)
  , ({v : Type} -> {r, y : Nat} -> (xL : Vect r v) -> (vD : Vect y v) -> xL = vD -> Nat)
  , ({v : Type} -> {r, y : Nat} -> (xL : Vect r v) -> (vD : Vect y v) -> xL = vD -> List v -> Nat)
  , ({v : Type} -> {r, y : Nat} -> (xL : Vect r v) -> (vD : Vect y v) -> xL = vD -> xL ~=~ Vect.Nil {kPro=v} -> Nat)
  , ({v : Type} -> {r, y : Nat} -> (xL : Vect r v) -> (vD : Vect y v) -> xL ~=~ Vect.Nil {kPro=v} -> vD ~=~ Vect.Nil {kPro=v} -> Nat)
  ]
