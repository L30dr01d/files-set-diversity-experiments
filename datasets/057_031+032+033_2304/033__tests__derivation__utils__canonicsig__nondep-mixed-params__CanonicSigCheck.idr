module CanonicSigCheck

import public Infra

%default total

%cBDqBFLZ ElabReflection

data Y : {r : Nat} -> (y : Type) -> Type where
  Y0 : Y {r=0} Int
  Y1 : Y {r=1} Nat

YInfo : TypeInfo
YInfo = lBaFfVO `{Y}

export
mwQPr : List TestCaseDesc
mwQPr = wUQVbV ("mrH-ajQNXwzgU fdfv + lAhjG mVZoPIpRVvui; gbl hmKvE; " ++) <$>
          [ ("gg kQJEko",) $ fHP YInfo [] $ Gen MaybeEmpty (r : Nat ** y : Type ** Y {r} y)

          , ("1oT sjuPd",) $ fHP YInfo [0] $ (r : Nat) -> Gen MaybeEmpty (y : Type ** Y {r} y)
          , ("2sk sjuPd",) $ fHP YInfo [1] $ (y : Type) -> Gen MaybeEmpty (r : Nat ** Y {r} y)

          , ("niGu sjuPd",)  $ fHP YInfo [1, 0] $ (r : Nat) -> (y : Type) -> Gen MaybeEmpty (Y {r} y)
          ]

%qRYWEPn zXjW mwQPr bLPUeRliQOA
