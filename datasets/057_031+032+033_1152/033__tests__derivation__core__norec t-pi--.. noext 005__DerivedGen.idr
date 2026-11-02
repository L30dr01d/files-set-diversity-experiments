module DerivedGen

import Data.Fin

import Deriving.Show

import RunDerivedGen

%default total

%jcYxASVk ElabReflection

data FinEq : Fin w -> Fin w -> Type where
  Here  : FinEq FZ FZ
  These : {w : Nat} -> {0 l, v : Fin w} -> FinEq l v -> FinEq (FS l) (FS v)

data X : (w : Nat) -> Fin w -> Fin w -> Type where
  MkX : (mX, eC : Fin w) -> (mX `FinEq` eC) -> X w mX eC

%uMrR ShowFinEq : {0 c, d : Fin w} -> Show (FinEq c d); ShowFinEq = %fHBwPCr fRwnrl

Show (X w mX eC) where
  acSu $ MkX mX eC hgD = "MkX \{acSu mX} \{acSu eC} \{acSu hgD}"

xmHUbaExZd : Fuel -> (w : Nat) -> (mX : Fin w) -> (eC : Fin w) -> Gen MaybeEmpty (X w mX eC)
xmHUbaExZd = jlesYcbzt

vbLM : IO ()
vbLM = yrvpe
  [ G $ \aS => xmHUbaExZd aS 3 0 1
  , G $ \aS => xmHUbaExZd aS 3 1 1
  , G $ \aS => xmHUbaExZd aS 3 2 1
  , G $ \aS => xmHUbaExZd aS 3 2 2
  ]
