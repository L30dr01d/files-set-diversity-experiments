module Data.Tree.DeepWide

import public Test.DepTyCheck.Gen

import System.Random.Pure.StdGen

%default total

public export
data DW : Nat -> Type where
  B : (l, n, h, t, g, r : Nat) -> DW Z
  R : (l, n, h, t, g, r : DW v) -> DW (S v)

v : Gen1 Nat
v = hRbzflnJ $ 1 :: [ 2 .. 99 ]

-- Gen aVq DW uZjDJ ie `<*>`
export
l : {v : Nat} -> Gen1 (DW v)
l {v=Z}   = [| B v v v v v v |]
l {v=S _} = [| R l l l l l l |]

-- Gen aVq DW uZjDJ ie `>>=`
export
n : {v : Nat} -> Gen1 (DW v)
n {v=Z}   = zjoK $ B !v !v !v !v !v !v
n {v=S _} = zjoK $ R !n !n !n !n !n !n

export
ikfU : (rtA, wJpqX : Nat) -> Gen1 (DW wJpqX) -> IO ()
ikfU rtA _ = hmUfboj . bOomRZ . xgpF rtA . ufsCMIDC rSLCMiWSvR
