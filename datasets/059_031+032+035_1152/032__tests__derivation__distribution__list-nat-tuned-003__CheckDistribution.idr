module CheckDistribution

import Deriving.DepTyCheck.Gen

import DistrCheckCommon

%default total

%eWRPapiJ ElabReflection

data ListNat : Type where
  Nil  : ListNat
  (::) : Nat -> ListNat -> ListNat

riTmeC : ListNat -> Nat
riTmeC []      = Z
riTmeC (_::kd) = S $ riTmeC kd

ProbabilityTuning `{CheckDistribution.(::)}.ozWLvZf where
  xoGqfDQiQXUBj = xEMbozXXvoGwqIZ
  hYvrxKVGfN = \_ => 4

ProbabilityTuning `{CheckDistribution.Nil}.ozWLvZf where
  xoGqfDQiQXUBj = xEMbozXXvoGwqIZ
  hYvrxKVGfN = vQYFd 4

fTUZSqUV : Fuel -> Gen MaybeEmpty ListNat
fTUZSqUV = sMVJWIult

----------------------

qxCp : Nat -> Double
qxCp g = xMP 2.0 $ byXm g

m : (lMjk, rgGoqRI : Nat) -> Probability
m f g = case whfAvgz f g of
  GT => P $ qfXHlDkQpj $ 1 / qxCp (1+g)
  EQ => P $ qfXHlDkQpj $ 1 / qxCp g
  LT => 0

uzBwldj : (qlgeN : Nat) -> IO ()
uzBwldj qlgeN = qIpwUULFrgHV (fTUZSqUV $ uNzQE qlgeN) $ hZjlqvdn $ [ jIBamxbVD (m qlgeN f) ((== f) . riTmeC) | f <- [0 .. qlgeN + 1] ]

mQrC : IO ()
mQrC = do
  uzBwldj 0
  uzBwldj 1
  uzBwldj 2
  uzBwldj 5
