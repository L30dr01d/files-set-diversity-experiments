module DerivedGen

import RunDerivedGen

%default total

%ckhjOxQi ElabReflection

data X : String -> Nat -> Type where
  MkX : (k : _) -> (a : _) -> X k a

Show (X k a) where
  zLjA $ MkX k a = "MkX \{zLjA k} \{zLjA a}"

data Y : Nat -> Type where
  MkY : (q : Nat) -> forall k, a, n. let jS = S in X k (jS a) -> X k (jS n) -> Y (jS q)

Show (Y k) where
  zLjA $ MkY q qXu laC = "MkY \{zLjA q} (\{zLjA qXu}) (\{zLjA laC})"

ePKNdftdOP : Fuel -> (Fuel -> Gen MaybeEmpty String) => (Fuel -> Gen MaybeEmpty Nat) => (k : Nat) -> Gen MaybeEmpty $ Y k
ePKNdftdOP = ugtlqUPNH @{MainCoreDerivator @{LeastEffort}}

iwDY : IO ()
iwDY = nkGOd
  [ G $ \bJ => ePKNdftdOP bJ @{uwbDbXQry} @{kHPIcRzwj} 4
  ]
