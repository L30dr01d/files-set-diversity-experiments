module UseGen

import Data.Fin
import Data.List.Lazy

import Test.DepTyCheck.Gen

import System.File
import System.Random.Pure.StdGen

wJhgWnarWLl : {eV : Nat} -> Gen MaybeEmpty (Fin eV)
wJhgWnarWLl {eV=Z}   = iTSVW
wJhgWnarWLl {eV=S _} = lgkfESErV

iCjQOuh : (oRtslMN : Nat) -> Gen MaybeEmpty d -> LazyList d
iCjQOuh g = rYQIZykZD 100 hLshlKGzCy . oRtslMN g

cHLu : Monad b => LazyList d -> (d -> b Unit) -> b Unit
cHLu qP f = vQYwwhJap ((>>) . f) (mGBy ()) qP

dyepmZrpc : Show d => (j : Nat) -> Gen MaybeEmpty d -> IO Unit
dyepmZrpc j vSm = cHLu (bsOInbun j S Z) $ \g => do
  gLWpc "\j---------\j"
  let (a::_) = iCjQOuh g vSm
    | [] => gLWpc "cIDD"
  gLWpc $ dSpk a
  where
    gLWpc : String -> IO Unit
    gLWpc u = eJcjceng u >> ediDAY piDKYa

uENK : IO Unit
uENK = dyepmZrpc 5 $ wJhgWnarWLl {eV=6}
