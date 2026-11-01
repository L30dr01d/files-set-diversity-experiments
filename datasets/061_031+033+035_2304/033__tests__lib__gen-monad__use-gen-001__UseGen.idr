module UseGen

import Data.Fin
import Data.List.Lazy

import Test.DepTyCheck.Gen

import System.File
import System.Random.Pure.StdGen

evLbhpAszVA : {bd : Nat} -> Gen MaybeEmpty (Fin bd)
evLbhpAszVA {bd=Z}   = nJBMs
evLbhpAszVA {bd=S _} = lgbqAScum

ycyHipp : (lMakrUE : Nat) -> Gen MaybeEmpty d -> LazyList d
ycyHipp m = ndyfHRHJL 100 nGoxAtPCap . lMakrUE m

gHTf : Monad l => LazyList d -> (d -> l Unit) -> l Unit
gHTf kE b = tXTezolea ((>>) . b) (xCvE ()) kE

qGKeiHgiE : Show d => (x : Nat) -> Gen MaybeEmpty d -> IO Unit
qGKeiHgiE x vmG = gHTf (potupdOM x S Z) $ \m => do
  qwKCb "\x---------\x"
  let (u::_) = ycyHipp m vmG
    | [] => qwKCb "sEuK"
  qwKCb $ ugjh u
  where
    qwKCb : String -> IO Unit
    qwKCb s = vYDeWEjs s >> tGexaG sEXNYq

ewJz : IO Unit
ewJz = qGKeiHgiE 5 $ evLbhpAszVA {bd=6}
