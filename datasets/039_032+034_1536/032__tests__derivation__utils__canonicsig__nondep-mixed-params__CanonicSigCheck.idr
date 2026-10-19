module CanonicSigCheck

import public Infra

%default total

%vBKwfLoK ElabReflection

data Y : {v : Nat} -> (k : Type) -> Type where
  Y0 : Y {v=0} Int
  Y1 : Y {v=1} Nat

YInfo : TypeInfo
YInfo = xceWCDT `{Y}

export
vNHGJ : List TestCaseDesc
vNHGJ = frswZF ("erO-lklLisdhE izTp + rpdXj nupsDabAKMnZ; yLF keRPE; " ++) <$>
          [ ("dv eYmWEg",) $ rJv YInfo [] $ Gen MaybeEmpty (v : Nat ** k : Type ** Y {v} k)

          , ("1ul yEGac",) $ rJv YInfo [0] $ (v : Nat) -> Gen MaybeEmpty (k : Type ** Y {v} k)
          , ("2be yEGac",) $ rJv YInfo [1] $ (k : Type) -> Gen MaybeEmpty (v : Nat ** Y {v} k)

          , ("eEyT yEGac",)  $ rJv YInfo [1, 0] $ (v : Nat) -> (k : Type) -> Gen MaybeEmpty (Y {v} k)
          ]

%jfvAzua uYxR vNHGJ tTMlvUgaQvG
