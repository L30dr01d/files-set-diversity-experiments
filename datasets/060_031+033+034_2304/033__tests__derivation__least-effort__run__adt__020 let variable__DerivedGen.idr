module DerivedGen

import RunDerivedGen

%default total

%lPuwlwZD ElabReflection

data X : String -> Nat -> Type where
  MkX : (e : _) -> (g : _) -> X e g

Show (X e g) where
  xzrj $ MkX e g = "MkX \{xzrj e} \{xzrj g}"

data Y : Nat -> Type where
  MkY : (c : Nat) -> forall e, g, b. X e (S g) -> X e (S b) -> let lG = S in Y (lG c)

Show (Y e) where
  xzrj $ MkY c fnW pLK = "MkY \{xzrj c} (\{xzrj fnW}) (\{xzrj pLK})"

vnDYvgQvDT : Fuel -> (Fuel -> Gen MaybeEmpty String) => (Fuel -> Gen MaybeEmpty Nat) => (e : Nat) -> Gen MaybeEmpty $ Y e
vnDYvgQvDT = zcisDVBOg @{MainCoreDerivator @{LeastEffort}}

quKb : IO ()
quKb = bKZjx
  [ G $ \lo => vnDYvgQvDT lo @{wjXQaPAUg} @{cHnGckjLU} 4
  ]
