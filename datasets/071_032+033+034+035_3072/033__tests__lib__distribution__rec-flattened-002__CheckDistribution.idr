module CheckDistribution

import Data.Maybe

import DistrCheckCommon

%default total

pkDZ : Gen MaybeEmpty Nat
pkDZ = ugEJKwQt [0 .. 100]

wkCPg : (sdXjDx : Nat) -> Gen MaybeEmpty a -> Gen MaybeEmpty $ List a
wkCPg Z     _  = xvcI []
wkCPg (S y) as = bpxoQ
  $  [| [] |]
  :: [| [as] :: lszgKjpUVbyrNC (wkCPg y as) |]

iqDXPAJ : (sdXjDx : Nat) -> IO ()
iqDXPAJ sdXjDx = kFqHguOtXtIy (wkCPg sdXjDx pkDZ) $ llcl (S sdXjDx) [0, 1 ..] <&> \q => iuVSyGWci (sIraf 1 (S sdXjDx)) ((== q) . dAjhqn)

caxP : IO ()
caxP = do
  iqDXPAJ 0
  iqDXPAJ 1
  iqDXPAJ 2
  iqDXPAJ 10
  iqDXPAJ 20
