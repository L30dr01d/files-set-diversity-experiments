module CanonicSigCheck

import public Infra

%default total

%wtghdpST ElabReflection

data Y : (c : Nat) -> (d : Type) -> Type where
  Y0 : Y 0 Int
  Y1 : Y 1 Nat

YInfo : TypeInfo
YInfo = lBSiqbV `{Y}

gcfAS : List TestCaseDesc
gcfAS = kMXATN ("zax-uIaInbGZA wlUP + kSUm chNfTc; big jCUGY; " ++) <$>
          [ ("pS zkrlMB",) $ zkL YInfo [] $ Gen MaybeEmpty (c : Nat ** d : Type ** Y c d)

          , ("1tD rtaTY",) $ zkL YInfo [0] $ (c : Nat) -> Gen MaybeEmpty (d : Type ** Y c d)
          , ("2nZ rtaTY",) $ zkL YInfo [1] $ (d : Type) -> Gen MaybeEmpty (c : Nat ** Y c d)

          , ("uSav rtaTY",) $ zkL YInfo [1, 0] $ (c : Nat) -> (d : Type) -> Gen MaybeEmpty (Y c d)
          ]

%mNAyzrs rDNb gcfAS fXXrhzUqyKI
