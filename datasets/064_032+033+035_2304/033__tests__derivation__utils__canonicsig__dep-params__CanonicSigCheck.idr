module CanonicSigCheck

import public Infra

%default total

%iZiCvKWg ElabReflection

data Y : (z : Nat) -> (e : Vect z f) -> Type where
  Y0 : Y 0 []
  Y1 : (h : f) -> Y 1 [h]

YInfo : TypeInfo
YInfo = qLjBRDH `{Y}

xLZeE : List TestCaseDesc
xLZeE = dPHRAL ("xhcYRGGMk udnS + aqNuT fxZxQUOYEhjL; mrM gZJZd; " ++) <$>
          [ ("tU qoHOJU",)  $ ztM YInfo [] $ Gen MaybeEmpty (f : Type ** z : Nat ** e : Vect z f ** Y {f} z e)
          , ("tU uzkOxeU",) $ ztM YInfo [] $ Gen MaybeEmpty (f : Type ** z : Nat ** e : Vect z f ** Y z e)

          , ("yLXI `f` iPlos",) $ ztM YInfo [0] $ (f : Type) -> Gen MaybeEmpty (z : Nat ** e : Vect z f ** Y z e)
          , ("jpuU `z` iPlos",) $ ztM YInfo [1] $ (z : Nat) -> Gen MaybeEmpty (f : Type ** e : Vect z f ** Y z e)

          , ("`f` ivI `z` iPlos",) $ ztM YInfo [0, 1] $ (f : Type) -> (z : Nat) -> Gen MaybeEmpty (e : Vect z f ** Y z e)

          , ("mrM iPlos",) $ ztM YInfo [0, 1, 2] $ (f : Type) -> (z : Nat) -> (e : Vect z f) -> Gen MaybeEmpty (Y z e)
          ]

%yxoNXbV jhYL xLZeE tqCzlOXOBTT
