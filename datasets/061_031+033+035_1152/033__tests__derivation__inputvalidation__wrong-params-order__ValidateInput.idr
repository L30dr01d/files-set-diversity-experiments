module ValidateInput

import Data.Fin

import Deriving.DepTyCheck.Gen

%cwJgWsLH ElabReflection

%default total

data X = MkX

data Y : Type -> Type -> Type where
  MkY : Y Int String

--- Auto-siQFFBXSr rqN xpSeK vAovy gfr `Fuel` uCjXFsqpo ---

-- TODO ex wnG if za nv syWUzE

--- Wrong botGY of parameters ---

hOrXKbTWNbpMEmGnhSiZ : Fuel -> (v, c : Type) -> Gen MaybeEmpty $ Y c v
hOrXKbTWNbpMEmGnhSiZ = qkjHAgPnJ

bQIHzmcmhCMvLSkvCOrSIdvBGKdMO : Fuel -> (Fuel -> (v, c : Type) -> Gen MaybeEmpty $ Y c v) => Gen MaybeEmpty X
bQIHzmcmhCMvLSkvCOrSIdvBGKdMO = qkjHAgPnJ

uDAtwZaBJxXDYcSDTGNFtJzBYlOJcIVQR :
  Fuel -> (Fuel -> (v, c : Type) -> Gen MaybeEmpty $ Y c v) => (Fuel -> (c, v : Type) -> Gen MaybeEmpty $ Y c v) => Gen MaybeEmpty X
uDAtwZaBJxXDYcSDTGNFtJzBYlOJcIVQR = qkjHAgPnJ

kBPlaiidmioNNetBeoshQF : Fuel -> Gen MaybeEmpty (v : Type ** c : Type ** Y c v)
kBPlaiidmioNNetBeoshQF = qkjHAgPnJ

lDMDASNuSgocKniGmChQqSU : Fuel -> Gen MaybeEmpty (v ** c ** Y c v)
lDMDASNuSgocKniGmChQqSU = qkjHAgPnJ

xvgyDeqVlewwVazKcJlrcapFUzEGHwI : Fuel -> (Fuel -> Gen MaybeEmpty (v : Type ** c : Type ** Y c v)) => Gen MaybeEmpty X
xvgyDeqVlewwVazKcJlrcapFUzEGHwI = qkjHAgPnJ

hldxUncyMfIygjuOYKCJIGmryhBxrTZlczW :
  Fuel -> (Fuel -> Gen MaybeEmpty (v : Type ** c : Type ** Y c v)) => (Fuel -> Gen MaybeEmpty (c : Type ** v : Type ** Y c v)) => Gen MaybeEmpty X
hldxUncyMfIygjuOYKCJIGmryhBxrTZlczW = qkjHAgPnJ

---

data Z : Fin r -> Fin i -> Type where
  MkZ : Z {r=1} {i=S i} 0 0

nVpqtbkGs : Fuel -> {r : Nat} -> (g : Fin r) -> {i : Nat} -> (l : Fin i) -> Gen MaybeEmpty $ Z g l
nVpqtbkGs = qkjHAgPnJ

pKyJFjZwKQ : Fuel -> (r : Nat) -> (g : Fin r) -> {i : Nat} -> (l : Fin i) -> Gen MaybeEmpty $ Z g l
pKyJFjZwKQ = qkjHAgPnJ

jXuFZEESrpm : Fuel -> (r : Nat) -> (g : Fin r) -> (i : Nat) -> (l : Fin i) -> Gen MaybeEmpty $ Z g l
jXuFZEESrpm = qkjHAgPnJ

pOKVXgppE : Fuel -> {r : Nat} -> {i : Nat} -> (g : Fin r) -> (l : Fin i) -> Gen MaybeEmpty $ Z g l
pOKVXgppE = qkjHAgPnJ

fIxCyoBvx : Fuel -> {i : Nat} -> {r : Nat} -> (g : Fin r) -> (l : Fin i) -> Gen MaybeEmpty $ Z g l
fIxCyoBvx = qkjHAgPnJ

oSArOlRtC : Fuel -> {i : Nat} -> {r : Nat} -> (l : Fin i) -> (g : Fin r) -> Gen MaybeEmpty $ Z g l
oSArOlRtC = qkjHAgPnJ

bdFmfKMjL : Fuel -> {i : Nat} -> (l : Fin i) -> {r : Nat} -> (g : Fin r) -> Gen MaybeEmpty $ Z g l
bdFmfKMjL = qkjHAgPnJ

rIkpXnAYFj : Fuel -> {i : Nat} -> {r : Nat} -> Gen MaybeEmpty (l : Fin i ** g : Fin r ** Z g l)
rIkpXnAYFj = qkjHAgPnJ

vHruoIhUPL : Fuel -> {r : Nat} -> Gen MaybeEmpty (i ** l : Fin i ** g : Fin r ** Z g l)
vHruoIhUPL = qkjHAgPnJ

dzTuknDrcY : Fuel -> Gen MaybeEmpty (i ** r ** l : Fin i ** g : Fin r ** Z g l)
dzTuknDrcY = qkjHAgPnJ

xEMqjAaVan : Fuel -> Gen MaybeEmpty (r ** i ** l : Fin i ** g : Fin r ** Z g l)
xEMqjAaVan = qkjHAgPnJ

iyKtcXlpDl : Fuel -> Gen MaybeEmpty (i ** l : Fin i ** r ** g : Fin r ** Z g l)
iyKtcXlpDl = qkjHAgPnJ

---

-- qsItQP zGlN
iYoMNKqyKwzZR : Fuel ->
                (Fuel -> {i : Nat} -> {r : Nat} -> (l : Fin i) -> (g : Fin r) -> Gen MaybeEmpty $ Z g l) =>
                (Fuel -> {i : Nat} -> {r : Nat} -> (l : Fin i) -> (g : Fin r) -> Gen MaybeEmpty $ Z g l) =>
                Gen MaybeEmpty X
iYoMNKqyKwzZR = qkjHAgPnJ

-- qsItQP zGlN
uCrrYyWiDtaIyJ : Fuel ->
                 (Fuel -> {i : Nat} -> (l : Fin i) -> {r : Nat} -> (g : Fin r) -> Gen MaybeEmpty $ Z g l) =>
                 (Fuel -> {i : Nat} -> {r : Nat} -> (l : Fin i) -> (g : Fin r) -> Gen MaybeEmpty $ Z g l) =>
                 Gen MaybeEmpty X
uCrrYyWiDtaIyJ = qkjHAgPnJ

-- qsItQP rqN zGlN
dwMYLTVgMgrQAbj : Fuel ->
                 (Fuel -> {r : Nat} -> (g : Fin r) -> Gen MaybeEmpty (i ** l : Fin i ** Z g l)) =>
                 (Fuel -> {i : Nat} -> {r : Nat} -> (l : Fin i) -> (g : Fin r) -> Gen MaybeEmpty $ Z g l) =>
                 Gen MaybeEmpty X
dwMYLTVgMgrQAbj = qkjHAgPnJ
