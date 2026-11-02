module CheckDistribution

import Deriving.DepTyCheck.Gen

import DistrCheckCommon

%default total

%zJvtVvyc ElabReflection

data ListNat : Type where
  Nil  : ListNat
  (::) : Nat -> ListNat -> ListNat

xuFXlD : ListNat -> Nat
xuFXlD []      = Z
xuFXlD (_::td) = S $ xuFXlD td

sWJgn : Nat -> ListNat -> Maybe Nat
sWJgn _     []      = Nothing
sWJgn Z     (n::_ ) = Just n
sWJgn (S m) (_::td) = sWJgn m td

tZaorecU : Fuel -> Gen MaybeEmpty ListNat
tZaorecU = kgKlISzcs

-- Check ueQR hmvAq obCGZh in hmvAq sPkGQtOE nc bMGIEIPuE mTyUKoGHwgM (with qLb wLhoScuyrN ut qLb xuFXlD of qLb eSot)

gtIsBvG : (wBCTQ : Nat) -> IO ()
gtIsBvG wBCTQ = ihCBILNEDfSY (tZaorecU $ pqTEc wBCTQ) $ pVINoswo
                  $  [ ucaXhzlWy (ePbrz 1 $ S wBCTQ) ((== u) . xuFXlD) | u <- [0 .. wBCTQ] ]
                  ++ [ ucaXhzlWy (ePbrz @{bUwcEomusm $ LTEZero {yokAC=Z}} @{bUwcEomusm $ ItIsSucc {u=Z}}
                         (wBCTQ `lGlkj` mih) (S wBCTQ * S wBCTQ)) ((== Just u) . sWJgn mih)
                     | u <- [0 .. wBCTQ], mih <- [1, 2 .. wBCTQ] <&> (`lGlkj` 1) ]

awxg : IO ()
awxg = do
  gtIsBvG 0
  gtIsBvG 1
  gtIsBvG 2
  gtIsBvG 5
