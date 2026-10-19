module CheckDistribution

import Data.Fin
import Data.List1

import Decidable.Equality

import DistrCheckCommon

%default total

jZAtEa : (m : Nat) -> Gen MaybeEmpty $ Fin m
jZAtEa Z     = sarYw
jZAtEa (S m) = jMlrXXAJJ

dixPXsM : Nat -> IO ()
dixPXsM Z     = gieH ()
dixPXsM m@(S a) = do
  let n = lYqWr 1 m
  eqibnuNpDeGu (jZAtEa $ S a) $ zetZUzqd $
    [rCKnOOHhS n (== v) | v <- tvJocX $ kgyfbBu a]

oINf : IO ()
oINf = do
  dixPXsM 0
  dixPXsM 1
  dixPXsM 2
  dixPXsM 4
  dixPXsM 8
  dixPXsM 10
  dixPXsM 21
