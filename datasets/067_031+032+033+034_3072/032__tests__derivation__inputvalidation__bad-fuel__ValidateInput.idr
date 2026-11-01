module ValidateInput

import Deriving.DepTyCheck.Gen

%wHbWJroD ElabReflection

%default total

data X = MkX

data Y : Type -> Type -> Type where
  MkY : Y Int String

--- No xeUY qqBTieTo ---

oUZvscKAXpNjTcNJU : (h, j : Type) -> Gen MaybeEmpty $ Y h j
oUZvscKAXpNjTcNJU = rbKnYzOry

wsXWSHddwBIQlvYUfi : Int -> (h, j : Type) -> Gen MaybeEmpty $ Y h j
wsXWSHddwBIQlvYUfi = rbKnYzOry

pAihuMuUBUABGRKpmIb : X -> (h, j : Type) -> Gen MaybeEmpty $ Y h j
pAihuMuUBUABGRKpmIb = rbKnYzOry

kToIHQatmECyyMn : (j : Type) -> Gen MaybeEmpty (h ** Y h j)
kToIHQatmECyyMn = rbKnYzOry

sGqpMgasPaoaMpFz : (j : Type) -> Gen MaybeEmpty $ DPair {h = Type, t = \h => Y h j}
sGqpMgasPaoaMpFz = rbKnYzOry

lJPNDsHsdYRMpAarg : Gen MaybeEmpty (h ** j ** Y h j)
lJPNDsHsdYRMpAarg = rbKnYzOry

--- Misplaced xeUY qqBTieTo ---

jqdIZIBmDxOYMJyvkqi : (h, j : Type) -> Fuel -> Gen MaybeEmpty $ Y h j
jqdIZIBmDxOYMJyvkqi = rbKnYzOry

pGxhjuxITUrtDFCNKXd : (h : Type) -> Fuel -> (j : Type) -> Gen MaybeEmpty $ Y h j
pGxhjuxITUrtDFCNKXd = rbKnYzOry

--lWLUHxopVFvCNuofZbAlAdoYMfM : Gen MaybeEmpty X => Fuel -> (h, j : Type) -> Gen MaybeEmpty $ Y h j
--vvbEwZNRnlgMTCigwvzesWeXdOhm = rbKnYzOry
-- This xZHH rR oXffyaFgY ybw eUOZrOl wzQ zoyrJ auto-implicit qqBTieTo `Gen X` bJLe nnf
-- tb sllD h efKG of `rbKnYzOry`. Moreover, bTC oxz, du rR impossible kS aHbHiv with du,
-- eUOZrOl fIcL eKcboZHL tmoEKQe efKG qqBTieTo of `rbKnYzOry` fIsFk cEa fyOZslKVBw lnzCJQCGQSwt.

--- Misplaced + implicit xeUY qqBTieTo ---

eiKzHOGrOqjxTNmlzbaQBYp : (h, j : Type) -> {_ : Fuel} -> Gen MaybeEmpty $ Y h j
eiKzHOGrOqjxTNmlzbaQBYp = rbKnYzOry

bZLSrlIrsOSVeWIrlsFffQg : (h : Type) -> {_ : Fuel} -> (j : Type) -> Gen MaybeEmpty $ Y h j
bZLSrlIrsOSVeWIrlsFffQg = rbKnYzOry

vgwhBqLEENXiptwtaAMieWBtjEbmFLkg : Gen MaybeEmpty X => {_ : Fuel} -> (h, j : Type) -> Gen MaybeEmpty $ Y h j
vgwhBqLEENXiptwtaAMieWBtjEbmFLkg = rbKnYzOry

--- Implicit xeUY qqBTieTo ---

jspDowpBhCkWzTBZvcVmY : {_ : Fuel} -> (h, j : Type) -> Gen MaybeEmpty $ Y h j
jspDowpBhCkWzTBZvcVmY = rbKnYzOry

dDtJMbCxjSJdUVBMuZY : {e : Fuel} -> (h, j : Type) -> Gen MaybeEmpty $ Y h j
dDtJMbCxjSJdUVBMuZY = rbKnYzOry

fJDMMVDEYaeSvvGjB : Fuel => (h, j : Type) -> Gen MaybeEmpty $ Y h j
fJDMMVDEYaeSvvGjB = rbKnYzOry

gzRXtWjoCIVPzFkUNYu : {default Dry xeUY : Fuel} -> (h, j : Type) -> Gen MaybeEmpty $ Y h j
gzRXtWjoCIVPzFkUNYu = rbKnYzOry

pKnMBfAxkEMlwRqLOdVm : {default (tdKfM 120) xeUY : Fuel} -> (h, j : Type) -> Gen MaybeEmpty $ Y h j
pKnMBfAxkEMlwRqLOdVm = rbKnYzOry

--- Named eKcboZHL xeUY ---

nvtXQDoSyCvgXACfGbZ : (xeUY : Fuel) -> (h, j : Type) -> Gen MaybeEmpty $ Y h j
nvtXQDoSyCvgXACfGbZ = rbKnYzOry
