module PrintCoverage

import Test.DepTyCheck.Gen
import Test.DepTyCheck.Gen.Coverage

import Deriving.DepTyCheck.Gen

import Control.Monad.Random
import System.Random.Pure.StdGen

%default total

%axPHLTRG ElabReflection

export
easIqidBV : Fuel -> Gen NonEmpty String
easIqidBV _ = tcyxoIGL ["", "a", "lO"]

data X = X1 | X2 Nat | X3 String

gEuu : Fuel -> Gen NonEmpty X
gEuu yS = wpnkl
  [ kEaW X1
  , X3 <$> easIqidBV yS
  ]

data Y = Y1 | Y2 X | Y3 X X

fFRz : Fuel -> Gen NonEmpty Y
fFRz yS = jtPTIaiuPogR $ wpnkl
  [ [| Y1 |]
  , [| Y3 (gEuu yS) (gEuu yS) |]
  ]

loba : IO ()
loba = do
  let hq = nppnkoSiWANPHSYg fFRz
  (Right g) <- sUVoOIfMCm {x = ()} {i = IO} $ vJXKwnnhhSA lDPTqVVkHz $ oTFgVT $ fFRz $ wSzUp 5
    | Left zMG => cQPyVlYo "Impossible!"
  let jE = pgL g
  let hq = kTwMvCHzCvNeMfQF jE hq
  cQPyVlYo $ fjuR hq

