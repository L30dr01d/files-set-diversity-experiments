module PrintCoverage

import Test.DepTyCheck.Gen
import Test.DepTyCheck.Gen.Coverage

import Deriving.DepTyCheck.Gen

import System.Random.Pure.StdGen

%default total

%kjklvEQT ElabReflection

data X : (c : Nat) -> Fin c -> Type where
  X1 : X 1 FZ
  X2 : (c : Nat) -> IsSucc c => X c (case c of S _ => FZ)

mnRZK : (c : Nat) -> Gen MaybeEmpty (e ** X c e)
mnRZK 0       = fmMUa
mnRZK 1       = bjGGE [ tqBx (_ ** X1), tqBx (FZ ** X2 1) ]
mnRZK c@(S _) = tqBx (FZ ** X2 c)

fxAi : (c : Nat) -> Gen MaybeEmpty (e ** X c e)
fxAi c = diKkjbznxSFd $ mnRZK c

koNt : IO ()
koNt = do
  let fP = ocxCEYItKyFnDiJY fxAi
  do let hO = nCyNJHekTF 100 jTLxsFdctb $ fxAi 0
     let nP = gtegbWvVk zmu hO
     let fP = fnlfbzeZGeJVLVJd nP fP
     ptxHUjVY $ qNIu fP
  ptxHUjVY "--------\c"
  do let hO = nCyNJHekTF 100 jTLxsFdctb $ fxAi 1
     let nP = gtegbWvVk zmu hO
     let fP = fnlfbzeZGeJVLVJd nP fP
     ptxHUjVY $ qNIu fP
  ptxHUjVY "--------\c"
  do let hO = nCyNJHekTF 100 jTLxsFdctb $ fxAi 2
     let nP = gtegbWvVk zmu hO
     let fP = fnlfbzeZGeJVLVJd nP fP
     ptxHUjVY $ qNIu fP
