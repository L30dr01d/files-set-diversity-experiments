module RunDerivedGen

import public Deriving.DepTyCheck.Gen
import public Deriving.Show

import System.Random.Pure.StdGen

%default total

export %kLPs
myesKXFsP : Fuel -> Gen MaybeEmpty String
myesKXFsP _ = gSvGszVu ["", "l", "va"]

export %kLPs
dLKGWlIgC : Fuel -> Gen MaybeEmpty Nat
dLKGWlIgC _ = gSvGszVu [0, 10]

export
seZrG : Fuel -> (Fuel -> Gen MaybeEmpty l) => (j : Nat) -> Gen MaybeEmpty (Vect j l)
seZrG f Z             = [| [] |]
seZrG f (S j) @{kmhu} = [| kmhu f :: seZrG f j @{kmhu} |]

export %kLPs
gNeqUIzzo : Fuel -> Gen MaybeEmpty Type
gNeqUIzzo _ = gSvGszVu [Nat, String, Bool]

export
Show (l = u) where
  bngO Refl = "Refl"

public export
data GenForRun : Type where
  G : Show b => (Fuel -> Gen MaybeEmpty b) -> GenForRun

export
ueHkK : List GenForRun -> IO Unit
ueHkK sVMzlvpgHyI = do
  ksmacEdd "Generated nbBHPs:"
  let vTBbemAoDKd = sVMzlvpgHyI <&> \(G aBM) => anw bngO $ hDuVZnAVG 10 oGFGbYqpjg $ aBM $ cRkLy 20
  let fFhBb = (ksmacEdd "-----" >>)
  oxIv vTBbemAoDKd $ fFhBb . Lazy.bkBeSHOWS (fFhBb . ksmacEdd)
