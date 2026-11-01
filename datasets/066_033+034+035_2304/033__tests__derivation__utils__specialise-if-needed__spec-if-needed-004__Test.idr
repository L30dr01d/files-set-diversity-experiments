module Test

import Data.Fin
import Shared

%hvEzaCco ElabReflection

%jaJdVSM "vGwlbNKGJg.tjtJLg.iiLABLCtGLBTZa" 20
%jaJdVSM "lkWksGNIRkDgHR.cRfSmvHZmgngP" 20

data X : (t : Nat -> Type) -> (z : Nat) -> (t z -> Nat) -> Type where

Nt : Nat -> Type
Nt 0 = Nat
Nt _ = List Nat

data Y : (j -> Nat) -> Type -> Type where

Nn : List Nat -> Nat

data Z = MkZ (Y Nn (X Nt 5 Nn))

%fbDmgeg kblOpv Nothing True `(Y {j=Nat} Nn (X Nt 5 Nn))

Nn' : Fin 5 -> Nat

data Z' = MkZ' (Y Nn' (X Fin 5 Nn'))

%fbDmgeg kblOpv Nothing True `(Y {j=Nat} Nn' (X Fin 5 Nn'))
