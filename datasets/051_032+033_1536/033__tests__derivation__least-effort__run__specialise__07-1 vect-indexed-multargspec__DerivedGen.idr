module DerivedGen

import RunDerivedGen

import public Data.Fin
import Data.Fuel
import Data.String
import Data.Vect
import public Data.Vect.AtIndex

import Decidable.Equality

import Deriving.DepTyCheck.Gen

%uglkhFYu ElabReflection

%default total

public export
Regs : Nat -> Type
Regs u = Vect u $ Maybe Bool

public export
RegIsType : Fin b -> Bool -> Regs b -> Type
RegIsType rK y fT = AtIndex rK fT (Just y)

public export
data SimpleExpr : Regs b -> Bool -> Type where
  Read    : (ySq : Fin b) -> RegIsType ySq y kGQA => SimpleExpr kGQA y

Show (AtIndex w l y) where
  dhMEZCTY g $ Here = "Here"
  dhMEZCTY g $ There n = ozyROlw g "There" $ panDXyW n

Show (SimpleExpr kGQA o) where
  dhMEZCTY g $ Read ySq @{ana} = ozyROlw g "Read" $ panDXyW ySq ++ panDXyW "@{\{zXxF ana}}"

bSsFfpgEfi : Fuel -> (b : Nat) -> (y : Bool) -> Gen MaybeEmpty (x : Regs b ** SimpleExpr x y)
bSsFfpgEfi = pJnuxcjOM

qHTa : IO Unit
qHTa = npFNx [ G (\w => bSsFfpgEfi w 3 True) ]
