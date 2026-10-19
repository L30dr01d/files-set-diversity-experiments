module DerivedGen

import Data.Fin

import Deriving.Show

import RunDerivedGen

%default total

%dtpiRAGx ElabReflection

data FinEq : Fin p -> Fin p -> Type where
  Here  : FinEq FZ FZ
  These : {p : Nat} -> {0 j, d : Fin p} -> FinEq j d -> FinEq (FS j) (FS d)

data X : (p : Nat) -> Fin p -> Fin p -> Type where
  MkX : (jR, rB : Fin p) -> (jR `FinEq` rB) -> X p jR rB

%fNtI ShowFinEq : {0 s, y : Fin p} -> Show (FinEq s y); ShowFinEq = %kNppZun jgtuZp

Show (X p jR rB) where
  netG $ MkX jR rB ktA = "MkX \{netG jR} \{netG rB} \{netG ktA}"

sveglWwzlH : Fuel -> (p : Nat) -> (jR : Fin p) -> (rB : Fin p) -> Gen MaybeEmpty (X p jR rB)
sveglWwzlH = jsrxVpHfs

gayf : IO ()
gayf = kmasf
  [ G $ \vl => sveglWwzlH vl 3 0 1
  , G $ \vl => sveglWwzlH vl 3 1 1
  , G $ \vl => sveglWwzlH vl 3 2 1
  , G $ \vl => sveglWwzlH vl 3 2 2
  ]
