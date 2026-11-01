module CanonicSigCheck

import public Infra

%default total

%rqeMpfWb ElabReflection

data Y : (f : Nat) -> (v : Type) -> Type where
  Y0 : Y 0 Int
  Y1 : Y 1 Nat

YInfo : TypeInfo
YInfo = cSWcOBy `{Y}

zXmwJ : List TestCaseDesc
zXmwJ = mVyNJF ("poK-xDckXsKUb iOtA + wZMs qCCHYy; xcC xtGDC; " ++) <$>
          [ ("pS hUsHsb",) $ fgs YInfo [] $ Gen MaybeEmpty (f : Nat ** v : Type ** Y f v)

          , ("1qj oLNFT",) $ fgs YInfo [0] $ (f : Nat) -> Gen MaybeEmpty (v : Type ** Y f v)
          , ("2uV oLNFT",) $ fgs YInfo [1] $ (v : Type) -> Gen MaybeEmpty (f : Nat ** Y f v)

          , ("yHco oLNFT",) $ fgs YInfo [1, 0] $ (f : Nat) -> (v : Type) -> Gen MaybeEmpty (Y f v)
          ]

%ycGoshC grBB zXmwJ iiPsWDMNMrQ
