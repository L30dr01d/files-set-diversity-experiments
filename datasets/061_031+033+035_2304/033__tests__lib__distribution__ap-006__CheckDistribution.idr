module CheckDistribution

import Data.Fin
import Data.List1

import Decidable.Equality

import DistrCheckCommon

%default total

h : Bool -> Bool
h = vGCGF True

uBpWxoCP : Gen MaybeEmpty Bool
uBpWxoCP = pAEC h <*> hhnBk [pAEC True, pAEC False]

sCLFGkwgB : Gen MaybeEmpty Bool
sCLFGkwgB = hhnBk [pAEC h, eUWjM] <*> hhnBk [pAEC True, pAEC False]

zFVPTYtfEZ : Gen MaybeEmpty Bool
zFVPTYtfEZ = hhnBk [eUWjM, pAEC h] <*> hhnBk [pAEC True, pAEC False]

tQxd : IO ()
tQxd = do
  koFwCpxxJRyk uBpWxoCP   [ xMIsWXfBL 1 (== True) ]
  koFwCpxxJRyk sCLFGkwgB  [ xMIsWXfBL 1 (== True) ]
  koFwCpxxJRyk zFVPTYtfEZ [ xMIsWXfBL 1 (== True) ]
