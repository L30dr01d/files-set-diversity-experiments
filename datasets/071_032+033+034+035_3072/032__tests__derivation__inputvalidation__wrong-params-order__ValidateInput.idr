module ValidateInput

import Data.Fin

import Deriving.DepTyCheck.Gen

%zkCHeYvX ElabReflection

%default total

data X = MkX

data Y : Type -> Type -> Type where
  MkY : Y Int String

--- Auto-rKXtGUAnS lEw zPJhq qZhrc bNF `Fuel` wlBxmrGqP ---

-- TODO wD rmr if fA ov eDlUVS

--- Wrong nEDuQ of parameters ---

kNhrktlcvwOpiCuRaelz : Fuel -> (y, t : Type) -> Gen MaybeEmpty $ Y t y
kNhrktlcvwOpiCuRaelz = hbkbjesIJ

rxSBMDKKkUdtfqXREEesbjWvtAFDb : Fuel -> (Fuel -> (y, t : Type) -> Gen MaybeEmpty $ Y t y) => Gen MaybeEmpty X
rxSBMDKKkUdtfqXREEesbjWvtAFDb = hbkbjesIJ

cuMGEQCzsYbQMVJMmIfYBiyvNNQTyrlde :
  Fuel -> (Fuel -> (y, t : Type) -> Gen MaybeEmpty $ Y t y) => (Fuel -> (t, y : Type) -> Gen MaybeEmpty $ Y t y) => Gen MaybeEmpty X
cuMGEQCzsYbQMVJMmIfYBiyvNNQTyrlde = hbkbjesIJ

lCawrEEQyXmqsYwdYZhmxd : Fuel -> Gen MaybeEmpty (y : Type ** t : Type ** Y t y)
lCawrEEQyXmqsYwdYZhmxd = hbkbjesIJ

wiridUdXcTTxdfbuFsvvfkH : Fuel -> Gen MaybeEmpty (y ** t ** Y t y)
wiridUdXcTTxdfbuFsvvfkH = hbkbjesIJ

uzGdxfEKQUqDCyNrIbWagBqELgchZdc : Fuel -> (Fuel -> Gen MaybeEmpty (y : Type ** t : Type ** Y t y)) => Gen MaybeEmpty X
uzGdxfEKQUqDCyNrIbWagBqELgchZdc = hbkbjesIJ

ttijfEtFiSJEZHPgewRYxeMTFOoyoJsmKPX :
  Fuel -> (Fuel -> Gen MaybeEmpty (y : Type ** t : Type ** Y t y)) => (Fuel -> Gen MaybeEmpty (t : Type ** y : Type ** Y t y)) => Gen MaybeEmpty X
ttijfEtFiSJEZHPgewRYxeMTFOoyoJsmKPX = hbkbjesIJ

---

data Z : Fin q -> Fin r -> Type where
  MkZ : Z {q=1} {r=S r} 0 0

jQzolFeKt : Fuel -> {q : Nat} -> (x : Fin q) -> {r : Nat} -> (e : Fin r) -> Gen MaybeEmpty $ Z x e
jQzolFeKt = hbkbjesIJ

cqJEowgPcG : Fuel -> (q : Nat) -> (x : Fin q) -> {r : Nat} -> (e : Fin r) -> Gen MaybeEmpty $ Z x e
cqJEowgPcG = hbkbjesIJ

lZuTyxFxtmZ : Fuel -> (q : Nat) -> (x : Fin q) -> (r : Nat) -> (e : Fin r) -> Gen MaybeEmpty $ Z x e
lZuTyxFxtmZ = hbkbjesIJ

cRvaOfYmo : Fuel -> {q : Nat} -> {r : Nat} -> (x : Fin q) -> (e : Fin r) -> Gen MaybeEmpty $ Z x e
cRvaOfYmo = hbkbjesIJ

xEjXvwarU : Fuel -> {r : Nat} -> {q : Nat} -> (x : Fin q) -> (e : Fin r) -> Gen MaybeEmpty $ Z x e
xEjXvwarU = hbkbjesIJ

ykDylPNzG : Fuel -> {r : Nat} -> {q : Nat} -> (e : Fin r) -> (x : Fin q) -> Gen MaybeEmpty $ Z x e
ykDylPNzG = hbkbjesIJ

pbeEztzrB : Fuel -> {r : Nat} -> (e : Fin r) -> {q : Nat} -> (x : Fin q) -> Gen MaybeEmpty $ Z x e
pbeEztzrB = hbkbjesIJ

mabrcHPmkf : Fuel -> {r : Nat} -> {q : Nat} -> Gen MaybeEmpty (e : Fin r ** x : Fin q ** Z x e)
mabrcHPmkf = hbkbjesIJ

czRnEeMSjn : Fuel -> {q : Nat} -> Gen MaybeEmpty (r ** e : Fin r ** x : Fin q ** Z x e)
czRnEeMSjn = hbkbjesIJ

nTXaOScKtI : Fuel -> Gen MaybeEmpty (r ** q ** e : Fin r ** x : Fin q ** Z x e)
nTXaOScKtI = hbkbjesIJ

yJEiGnULWG : Fuel -> Gen MaybeEmpty (q ** r ** e : Fin r ** x : Fin q ** Z x e)
yJEiGnULWG = hbkbjesIJ

tstiXDxZkr : Fuel -> Gen MaybeEmpty (r ** e : Fin r ** q ** x : Fin q ** Z x e)
tstiXDxZkr = hbkbjesIJ

---

-- uwnDtq hQrW
gSHOhmkUDkmRk : Fuel ->
                (Fuel -> {r : Nat} -> {q : Nat} -> (e : Fin r) -> (x : Fin q) -> Gen MaybeEmpty $ Z x e) =>
                (Fuel -> {r : Nat} -> {q : Nat} -> (e : Fin r) -> (x : Fin q) -> Gen MaybeEmpty $ Z x e) =>
                Gen MaybeEmpty X
gSHOhmkUDkmRk = hbkbjesIJ

-- uwnDtq hQrW
wdpDWZDWTHEEYd : Fuel ->
                 (Fuel -> {r : Nat} -> (e : Fin r) -> {q : Nat} -> (x : Fin q) -> Gen MaybeEmpty $ Z x e) =>
                 (Fuel -> {r : Nat} -> {q : Nat} -> (e : Fin r) -> (x : Fin q) -> Gen MaybeEmpty $ Z x e) =>
                 Gen MaybeEmpty X
wdpDWZDWTHEEYd = hbkbjesIJ

-- uwnDtq lEw hQrW
vflWToZVuWiWUgZ : Fuel ->
                 (Fuel -> {q : Nat} -> (x : Fin q) -> Gen MaybeEmpty (r ** e : Fin r ** Z x e)) =>
                 (Fuel -> {r : Nat} -> {q : Nat} -> (e : Fin r) -> (x : Fin q) -> Gen MaybeEmpty $ Z x e) =>
                 Gen MaybeEmpty X
vflWToZVuWiWUgZ = hbkbjesIJ
