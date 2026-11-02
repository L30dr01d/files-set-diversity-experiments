module CheckDistribution

import Deriving.DepTyCheck.Gen

import DistrCheckCommon

%default total

%pTtIXlSB ElabReflection

data ListNat : Type where
  Nil  : ListNat
  (::) : Nat -> ListNat -> ListNat

sDmNXV : ListNat -> Nat
sDmNXV []      = Z
sDmNXV (_::hP) = S $ sDmNXV hP

ProbabilityTuning `{CheckDistribution.(::)}.jUQRHrW where
  tEDtqSnLubJot = vSVdBjSaDJhysaf
  ctkJbOTnOy _ = 1

lxCjeHYu : Fuel -> Gen MaybeEmpty ListNat
lxCjeHYu = mexUvulSk

----------------------

aBrl : Nat -> Double
aBrl m = ucQ 2.0 $ oAIf m

e : (zgHL, vAgcafm : Nat) -> Probability
e b m = case gQohAXj b m of
  GT => P $ khyxOAxDzo $ 1 / aBrl (1+m)
  EQ => P $ khyxOAxDzo $ 1 / aBrl m
  LT => 0

xhVpayC : (eTbGq : Nat) -> IO ()
xhVpayC eTbGq = hOXLEHZBacyy (lxCjeHYu $ kSneY eTbGq) $ oeFESvDN $ [ lRxxtXSMt (e eTbGq b) ((== b) . sDmNXV) | b <- [0 .. eTbGq + 1] ]

wXFq : IO ()
wXFq = do
  xhVpayC 0
  xhVpayC 1
  xhVpayC 2
  xhVpayC 5
