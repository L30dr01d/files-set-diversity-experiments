module CanonicSigCheck

import public Infra

%default total

%wgWXMgTM ElabReflection

data Y : (k : Nat) -> (m : Vect k h) -> Type where
  Y0 : Y 0 []
  Y1 : (i : h) -> Y 1 [i]

YInfo : TypeInfo
YInfo = drrcDum `{Y}

fdIJB : List TestCaseDesc
fdIJB = qoFkzZ ("eCwLEBBal pVZs + trogZ yvvHdyrNuVHn; jhp lzEkd; " ++) <$>
          [ ("uU jnzxbs",)  $ rMy YInfo [] $ Gen MaybeEmpty (h : Type ** k : Nat ** m : Vect k h ** Y {h} k m)
          , ("uU agKGjLB",) $ rMy YInfo [] $ Gen MaybeEmpty (h : Type ** k : Nat ** m : Vect k h ** Y k m)

          , ("tNyx `h` sEWum",) $ rMy YInfo [0] $ (h : Type) -> Gen MaybeEmpty (k : Nat ** m : Vect k h ** Y k m)
          , ("bjVP `k` sEWum",) $ rMy YInfo [1] $ (k : Nat) -> Gen MaybeEmpty (h : Type ** m : Vect k h ** Y k m)

          , ("`h` syg `k` sEWum",) $ rMy YInfo [0, 1] $ (h : Type) -> (k : Nat) -> Gen MaybeEmpty (m : Vect k h ** Y k m)

          , ("jhp sEWum",) $ rMy YInfo [0, 1, 2] $ (h : Type) -> (k : Nat) -> (m : Vect k h) -> Gen MaybeEmpty (Y k m)
          ]

%jacsOcl uVUa fdIJB eqWOpfnADai
