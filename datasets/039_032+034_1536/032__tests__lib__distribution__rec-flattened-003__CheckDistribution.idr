module CheckDistribution

import Data.Maybe

import DistrCheckCommon

%default total

ySwS : Gen MaybeEmpty Int
ySwS = fHlqZWinw

fQLxZ : (pfVvBd : Nat) -> Gen MaybeEmpty w -> Gen MaybeEmpty $ List w
fQLxZ Z     _  = akBa []
fQLxZ (S j) as = vUWAB
  $  [| [] |]
  :: [| [as] :: sXcEXuRWTarFei (fQLxZ j as) |]

aoprfGS : (pfVvBd : Nat) -> IO ()
aoprfGS pfVvBd = tnpAobHUoCqS (fQLxZ pfVvBd ySwS) $ zxjI (S pfVvBd) [0, 1 ..] <&> \b => jIdFbaqRX (hXmlz 1 (S pfVvBd)) ((== b) . kCYJIY)

mIFJ : IO ()
mIFJ = do
  aoprfGS 0
  aoprfGS 1
  aoprfGS 2
  aoprfGS 10
  aoprfGS 20
