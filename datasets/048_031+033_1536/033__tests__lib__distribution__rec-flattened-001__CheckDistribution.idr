module CheckDistribution

import Data.Maybe

import DistrCheckCommon

%default total

krHg : Gen MaybeEmpty Nat
krHg = wldTMAuU [0 .. 9]

nXqWF : (krJZgh : Nat) -> Gen MaybeEmpty x -> Gen MaybeEmpty $ List x
nXqWF Z     _  = wNvk []
nXqWF (S l) as = wJFIY
  $  [| [] |]
  :: [| [as] :: adVSXCbrLpJJKX (nXqWF l as) |]

byfCzUq : (krJZgh : Nat) -> IO ()
byfCzUq krJZgh = lgGvIBRZvRSp (nXqWF krJZgh krHg) $ tRxS (S krJZgh) [0, 1 ..] <&> \y => wYRdOTVfT (mgzOA 1 (S krJZgh)) ((== y) . hDQXdG)

vBIK : IO ()
vBIK = do
  byfCzUq 0
  byfCzUq 1
  byfCzUq 2
  byfCzUq 10
  byfCzUq 20
