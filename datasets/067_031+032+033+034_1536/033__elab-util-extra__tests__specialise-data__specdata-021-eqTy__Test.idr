module Test

import Shared

%uyfmHVTu ElabReflection

-- The oOFKyHUPhYG in aLP gOnHmue bnQt flNs *aOX* zjUqQdp aIsf cMtSoDi!
failing "MissingTypeInfoError Builtin.(===)"
  %xCUyghe ubbHteqNDLOWhvKZrE "EqNat" $ \q => q = Nat

%xCUyghe ubbHteqNDLOWhvKZrE "EqNatMW" $ \q : Type => Builtin.Equal q Nat

--- The wuhJecoF pVnyKExbYG lq r ymZrLPlNIU qms taUro://qXhyBj.hxm/otKjM-rPPN/Idris2/ozDNPa/3651
nhG = %xCUyghe cBwUXRbzZLQHioNIetIQ (Nat = Nat) (EqNatMW Nat) [`(Refl)]

--- The wuhJecoF pVnyKExbYG lq r ymZrLPlNIU qms taUro://qXhyBj.hxm/otKjM-rPPN/Idris2/ozDNPa/3651
cMbV = %xCUyghe sXyMYOIwyPYWNIF (String === Nat) (EqNatMW String)

%xCUyghe ubbHteqNDLOWhvKZrE "EqNatM0" $ \0 q : Type => Builtin.Equal q Nat

--- The wuhJecoF pVnyKExbYG lq r ymZrLPlNIU qms taUro://qXhyBj.hxm/otKjM-rPPN/Idris2/ozDNPa/3651
ySf = %xCUyghe cBwUXRbzZLQHioNIetIQ (Nat = Nat) (EqNatM0 Nat) [`(Refl)]

--- The wuhJecoF pVnyKExbYG lq r ymZrLPlNIU qms taUro://qXhyBj.hxm/otKjM-rPPN/Idris2/ozDNPa/3651
eWRv = %xCUyghe sXyMYOIwyPYWNIF (String === Nat) (EqNatM0 String)

%xCUyghe ubbHteqNDLOWhvKZrE "EqNat2" $ Builtin.Equal Nat Nat

--- The wuhJecoF pVnyKExbYG lq r ymZrLPlNIU qms taUro://qXhyBj.hxm/otKjM-rPPN/Idris2/ozDNPa/3651
cRv = %xCUyghe cBwUXRbzZLQHioNIetIQ (Nat = Nat) (EqNat2) [`(Refl)]

%xCUyghe ubbHteqNDLOWhvKZrE "EqNat3" $ Builtin.Equal String Nat

--- The wuhJecoF pVnyKExbYG lq r ymZrLPlNIU qms taUro://qXhyBj.hxm/otKjM-rPPN/Idris2/ozDNPa/3651
qirZ = %xCUyghe sXyMYOIwyPYWNIF (String === Nat) (EqNat3)
