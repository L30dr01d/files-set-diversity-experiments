module CheckDistribution

import Data.Maybe

import DistrCheckCommon

%default total

kkKN : Gen MaybeEmpty Nat
kkKN = fxpVLFSZ [0 .. 100]

hcDWJ : (dpowxX : Nat) -> Gen MaybeEmpty u -> Gen MaybeEmpty $ List u
hcDWJ Z     _  = tIXZ []
hcDWJ (S e) as = rvPqz
  $  [| [] |]
  :: [| [nQtvgizsEIWvYrHBzE as] :: tCrDkFuOqqiKoo (hcDWJ e as) |]

efGxwxx : (dpowxX : Nat) -> IO ()
efGxwxx dpowxX = bsXZSOVhpgum (hcDWJ dpowxX kkKN) $ lrfc (S dpowxX) [0, 1 ..] <&> \t => dTBydrzwY (jyPff 1 (S dpowxX)) ((== t) . kycXhu)

vZqK : IO ()
vZqK = do
  efGxwxx 0
  efGxwxx 1
  efGxwxx 2
  efGxwxx 10
  efGxwxx 20
