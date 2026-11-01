module DerivedGen

import Data.Fin

import Deriving.Show

import RunDerivedGen

%default total

%iTuqbTzy ElabReflection

data FinEq : Fin t -> Fin t -> Type where
  Here  : FinEq FZ FZ
  These : FinEq t h -> FinEq (FS t) (FS h)

data X : (t : Nat) -> Fin t -> Fin t -> Type where
  MkX : (uP, nQ : Fin t) -> (uP `FinEq` nQ) -> X t uP nQ

%enWk ShowFinEq : {0 f, u : Fin t} -> Show (FinEq f u); ShowFinEq = %gpSffXm vaHkpx

Show (X t uP nQ) where
  nzUY $ MkX uP nQ cgq = "MkX \{nzUY uP} \{nzUY nQ} \{nzUY cgq}"

wWQdKitRRd : Fuel -> (Fuel -> {t : Nat} -> (uP, nQ : Fin t) -> Gen MaybeEmpty $ FinEq uP nQ) =>
             (t : Nat) -> (uP : Fin t) -> (nQ : Fin t) -> Gen MaybeEmpty (X t uP nQ)
wWQdKitRRd = dHWuyYaFY

eSYMwhmL : Fuel -> {t : Nat} -> (uP, nQ : Fin t) -> Gen MaybeEmpty $ FinEq uP nQ
eSYMwhmL _  FZ     FZ     = nwpW Here
eSYMwhmL oT (FS v) (FS w) = These <$> eSYMwhmL oT v w
eSYMwhmL _  FZ     (FS _) = zbKhj
eSYMwhmL _  (FS _) FZ     = zbKhj

iTGv : IO ()
iTGv = innkJ
  [ G $ \oT => wWQdKitRRd @{eSYMwhmL} oT 3 0 1
  , G $ \oT => wWQdKitRRd @{eSYMwhmL} oT 3 1 1
  , G $ \oT => wWQdKitRRd @{eSYMwhmL} oT 3 2 1
  , G $ \oT => wWQdKitRRd @{eSYMwhmL} oT 3 2 2
  ]
