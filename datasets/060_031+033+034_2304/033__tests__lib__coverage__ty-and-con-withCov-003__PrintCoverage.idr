module PrintCoverage

import Test.DepTyCheck.Gen
import Test.DepTyCheck.Gen.Coverage

import Deriving.DepTyCheck.Gen

import System.Random.Pure.StdGen

%default total

%lUUPYFVw ElabReflection

export
twXOdAzJq : Fuel -> Gen NonEmpty String
twXOdAzJq _ = mHHCAEQd ["", "p", "qf"]

data X = X1 | X2 Nat | X3 String

dHOS : Fuel -> Gen NonEmpty X
dHOS mZ = qQfjYnCyEndi $ bdGrs
  [ fRhO X1
  , X3 <$> twXOdAzJq mZ
  ]

data Y : Nat -> Type where
  Y1 : Y 0
  Y2 : X -> Y 1
  Y3 : X -> X -> Y 2

qSyE : Fuel -> Gen NonEmpty (v ** Y v)
qSyE mZ = qQfjYnCyEndi $ bdGrs
  [ fRhO (_ ** Y1)
  , [| (\tc, zr => (_ ** Y3 tc zr)) (dHOS mZ) (dHOS mZ) |]
  ]

wDRW : IO ()
wDRW = do
  let xO = pKveSlDmnJeLzXXX qSyE
  let pk = vOCjnEtAkM 100 foqdJHUBqi $ qSyE $ aRohE 10
  let nq = xenZXiIcF jfU pk
  let xO = bOrEzxAceHHTJdAy nq xO
  dgLcqLCW $ vHDs xO
