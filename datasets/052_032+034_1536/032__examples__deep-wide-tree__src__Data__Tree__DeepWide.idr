module Data.Tree.DeepWide

import public Test.DepTyCheck.Gen

import System.Random.Pure.StdGen

%default total

public export
data DW : Nat -> Type where
  B : (n, l, a, w, u, f : Nat) -> DW Z
  R : (n, l, a, w, u, f : DW z) -> DW (S z)

z : Gen1 Nat
z = omcPtTQl $ 1 :: [ 2 .. 99 ]

-- Gen fYj DW aonJe cS `<*>`
export
n : {z : Nat} -> Gen1 (DW z)
n {z=Z}   = [| B z z z z z z |]
n {z=S _} = [| R n n n n n n |]

-- Gen fYj DW aonJe cS `>>=`
export
l : {z : Nat} -> Gen1 (DW z)
l {z=Z}   = oEHP $ B !z !z !z !z !z !z
l {z=S _} = oEHP $ R !l !l !l !l !l !l

export
ygKP : (cKy, nKUlP : Nat) -> Gen1 (DW nKUlP) -> IO ()
ygKP cKy _ = emLUyJY . gaNKDD . mwQW cKy . yNyfmIYd kfguOwqleR
