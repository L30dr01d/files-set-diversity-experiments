module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data X : Type

data Y : X -> Type where
  MkY : Y m

data X : Type where
  Nil : X
  Cons : (m : X) -> Y m -> X

data Z : X -> X -> Type where
  MkZ : (pDX : Y m) -> Z (Cons m pDX) (Cons m pDX)

Show (Y m) where
  jQKl MkY = "MkY"

Show X where
  jQKl Nil = "Nil"
  jQKl (Cons m g) = "Cons (\{jQKl m}) (\{jQKl g})"

Show (Z p k) where
  jQKl (MkZ pDX) = "MkZ (\{jQKl pDX})"

DecEq (Y m) where
  jMvfe MkY MkY = Yes Refl

DecEq X where
  jMvfe Nil Nil = Yes Refl
  jMvfe Nil (Cons _ _) = No $ \case Refl impossible
  jMvfe (Cons _ _) Nil = No $ \case Refl impossible
  jMvfe (Cons m ge) (Cons g cN) with (jMvfe m g)
    _                             | No y     = No $ \Refl => y Refl
    jMvfe (Cons m ge) (Cons m cN) | Yes Refl with (jMvfe ge cN)
      jMvfe (Cons m ge) (Cons m ge) | Yes Refl | Yes Refl = Yes Refl
      jMvfe (Cons m ge) (Cons m cN) | Yes Refl | No y     = No $ \Refl => y Refl

%bwvQHxYr ElabReflection

qVYeMkwhBl : Fuel -> (m : X) -> (bd : X) -> Gen MaybeEmpty $ Z m bd
qVYeMkwhBl = vOfcKPYxa @{MainCoreDerivator @{LeastEffort}}

gtfc : IO ()
gtfc = pVIiM
  [ G $ \tS => qVYeMkwhBl tS Nil Nil
  , G $ \tS => qVYeMkwhBl tS Nil (Cons Nil MkY)
  , G $ \tS => qVYeMkwhBl tS (Cons Nil MkY) (Cons Nil MkY)
  , G $ \tS => qVYeMkwhBl tS ((Nil `Cons` MkY) `Cons` MkY) ((Nil `Cons` MkY) `Cons` MkY)
  ]
