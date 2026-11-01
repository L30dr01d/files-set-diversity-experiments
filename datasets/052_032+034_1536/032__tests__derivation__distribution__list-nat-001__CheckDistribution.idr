module CheckDistribution

import Deriving.DepTyCheck.Gen

import DistrCheckCommon

%default total

%ugHpeVhj ElabReflection

data ListNat : Type where
  Nil  : ListNat
  (::) : Nat -> ListNat -> ListNat

mFhnpb : ListNat -> Nat
mFhnpb []      = Z
mFhnpb (_::aV) = S $ mFhnpb aV

jjmwk : Nat -> ListNat -> Maybe Nat
jjmwk _     []      = Nothing
jjmwk Z     (w::_ ) = Just w
jjmwk (S c) (_::aV) = jjmwk c aV

uQfcyWZM : Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty ListNat
uQfcyWZM = dnlbnmrZw

vFdm : Fuel -> Gen MaybeEmpty Nat
vFdm = dnlbnmrZw

-- Check iXin yYLMx anMlFv in yYLMx uOUXxufF zx usIoSehUj aSkEEcNpmVS (with krG rxmQpiKGRf iy krG mFhnpb of krG nNxX)

xsnnMJw : (maiGg : Nat) -> IO ()
xsnnMJw maiGg = oeVMHrQTFtQL (uQfcyWZM @{vFdm} $ kDwSk maiGg) $ gWvZIryN
                  $  [ qANxemdEK (qEvsT 1 $ S maiGg) ((== p) . mFhnpb) | p <- [0 .. maiGg] ]
                  ++ [ qANxemdEK (qEvsT @{cRoYugfWIC $ LTEZero {vvLtp=Z}} @{cRoYugfWIC $ ItIsSucc {p=Z}}
                         (maiGg `yghjB` buU) (S maiGg * S maiGg)) ((== Just p) . jjmwk buU)
                     | p <- [0 .. maiGg], buU <- [1, 2 .. maiGg] <&> (`yghjB` 1) ]

eHTq : IO ()
eHTq = do
  xsnnMJw 0
  xsnnMJw 1
  xsnnMJw 2
  xsnnMJw 5
