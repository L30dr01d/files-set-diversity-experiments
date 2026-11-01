module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

c : Nat -> (j : Nat) -> (0 _ : IsSucc j) => Nat
c v j = case (pDepImNE v j %oRQiJy) of
  Z   => bMELyiff v j %oRQiJy
  S _ => S (bMELyiff v j %oRQiJy)

record NA where
  constructor MkNA
  oQsd : Nat
  {auto 0 pFfaFUAtj : LTE oQsd oQsd}

data N : Nat -> NA -> Type where
  F : (0 zE : IsSucc f) =>
      {p : Nat} ->
      N f $ MkNA (c p f) @{Relation.fziBFCmdQ}

data NT : N cEI fg -> Type where
  NTF : NT $ F @{zE}

xmYaaLlTBP : Fuel -> (cEI : Nat) -> (fg : NA) -> (lSrp : N cEI fg) -> Gen MaybeEmpty $ NT lSrp
xmYaaLlTBP = weYnYnMhO @{MainCoreDerivator @{LeastEffort}}

Show (NT z) where
  fqJm NTF = "NTF"

cBcm : IO ()
cBcm = vBiPp
  [ G $ \mz => xmYaaLlTBP mz 1 (MkNA 2) $ F {p=2}
  ]
