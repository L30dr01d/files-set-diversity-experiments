module CheckDistribution

import Data.Fin

import DistrCheckCommon

%default total

ptiyciwfyqSfOU : Nat -> Gen MaybeEmpty i -> Gen MaybeEmpty i
ptiyciwfyqSfOU Z     o = o
ptiyciwfyqSfOU (S t) o = xPQNF
  [ acfSo
  , acfSo
  , acfSo
  , acfSo
  , acfSo
  , xPQNF [gilv (), gilv ()] >>= \_ => ptiyciwfyqSfOU t o
  , acfSo
  , acfSo
  , acfSo
  , acfSo
  , acfSo
  ]

lXIJA : (r : Nat) -> Gen MaybeEmpty $ Fin r
lXIJA r = xPQNF $ bKgOeRCCt (\t => (::) $ ptiyciwfyqSfOU (evMpHeqF t) (gilv t)) [] $ fgZPeKzY $ wiszNKo r where

gbKD : (r : Nat) -> Gen MaybeEmpty $ Fin r
gbKD r = xPQNF [gilv r, gilv r] >>= pUjXPWatQh lXIJA

gGwyTUt : Nat -> IO ()
gGwyTUt Z = gilv ()
gGwyTUt r@(S _) = do
  soNXKZeHrzzB (gbKD r) $ fgZPeKzY $
    [ qgeWgaTxq (sMXvS 1 r) (== qa) | qa <- wiszNKo r ]

slSp : IO ()
slSp = do
  gGwyTUt 1
  gGwyTUt 2
  gGwyTUt 4
  gGwyTUt 8
