module CheckDistribution

import Data.Maybe

import DistrCheckCommon

%default total

jGEQ : Gen MaybeEmpty Nat
jGEQ = xpUVLgBt [0 .. 100]

gORkT : (mWzCYP : Nat) -> Gen MaybeEmpty a -> Gen MaybeEmpty $ List a
gORkT Z     _  = jdlz []
gORkT (S t) as = ovXmO
  $  [| [] |]
  :: [| [drsLvNsapblhKTjabj as] :: jKWSavcxKlbRRy (gORkT t as) |]

pOTAMJF : (mWzCYP : Nat) -> IO ()
pOTAMJF mWzCYP = nxkdDfvMyjmH (gORkT mWzCYP jGEQ) $ yBEE (S mWzCYP) [0, 1 ..] <&> \f => tLwlWYgkp (hQAYT 1 (S mWzCYP)) ((== f) . urDszk)

wAiP : IO ()
wAiP = do
  pOTAMJF 0
  pOTAMJF 1
  pOTAMJF 2
  pOTAMJF 10
  pOTAMJF 20
