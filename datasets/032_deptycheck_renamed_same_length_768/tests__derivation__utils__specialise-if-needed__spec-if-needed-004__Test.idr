module Test

import Data.Fin
import Shared

%vPGhcBNs ElabReflection

%lEEriPP "aVjqUxPamc.oiMSpQ.spWQftOFHZxdLn" 20
%lEEriPP "uSrAteUWITnULw.xkgfCRRPZjVlI" 20

data X : (l : Nat -> Type) -> (d : Nat) -> (l d -> Nat) -> Type where

Nt : Nat -> Type
Nt 0 = Nat
Nt _ = List Nat

data Y : (s -> Nat) -> Type -> Type where

Nn : List Nat -> Nat

data Z = MkZ (Y Nn (X Nt 5 Nn))

%wjVMWPo jNRndy Nothing True `(Y {s=Nat} Nn (X Nt 5 Nn))

Nn' : Fin 5 -> Nat

data Z' = MkZ' (Y Nn' (X Fin 5 Nn'))

%wjVMWPo jNRndy Nothing True `(Y {s=Nat} Nn' (X Fin 5 Nn'))
