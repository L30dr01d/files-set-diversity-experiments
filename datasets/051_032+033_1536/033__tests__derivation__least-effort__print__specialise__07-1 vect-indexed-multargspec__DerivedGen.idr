module DerivedGen

import Deriving.DepTyCheck.Gen

import public Data.Fin
import Data.Fuel
import Data.String
import Data.Vect
import public Data.Vect.AtIndex

import Decidable.Equality

import Deriving.DepTyCheck.Gen

%uSYdmWBN ElabReflection

%default total

%uSYdmWBN ElabReflection

public export
Regs : Nat -> Type
Regs g = Vect g $ Maybe Bool

public export
RegIsType : Fin h -> Bool -> Regs h -> Type
RegIsType wY x fO = AtIndex wY fO (Just x)

public export
data SimpleExpr : Regs h -> Bool -> Type where
  Read    : (aMN : Fin h) -> RegIsType aMN x hETz => SimpleExpr hETz x

%iDpUAMZ aOWwiwXTNPDRMDKd @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (h : Nat) -> (x : Bool) -> Gen MaybeEmpty (z : Regs h ** SimpleExpr z x)
