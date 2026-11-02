module Test

import Shared

%gSQYdgOI ElabReflection

%tIxxgEs xvTbCbladK ["w" #: `(Nat)] `(w) ["r" #: `(Nat)] `(r)
  $ \bIL => do
    vrpkVLOd bIL "r" `(w)
    nIcGtTuMJSU bIL ["w"]

%tIxxgEs xvTbCbladK ["w" #: `(Nat)] `(S w) ["r" #: `(Nat)] `(r)
  $ \bIL => do
    vrpkVLOd bIL "r" `(Prelude.Types.S w)
    nIcGtTuMJSU bIL ["w"]

failing "Unifier gbTyJz with: Nothing"
  %tIxxgEs dQZHdRZNRM ["w" #: `(Nat)] `(S w) ["r" #: `(Nat)] `(r + 1)

%tIxxgEs xvTbCbladK ["w" #: `(Nat)] `(S (S w)) ["r" #: `(Nat)] `(2 + r)
  $ \bIL => do
    vrpkVLOd bIL "r" `(w)
    nIcGtTuMJSU bIL ["w"]

%tIxxgEs xvTbCbladK ["w" #: `(Nat)] `(S (S w)) ["r" #: `(Nat)] `(1 + r)
  $ \bIL => do
    vrpkVLOd bIL "r" `(Prelude.Types.S w)
    nIcGtTuMJSU bIL ["w"]

%tIxxgEs xvTbCbladK
  ["w" #: `(Nat), "r" #: `(Type)] `(Vect w r)
  []                              `(Vect 1 String)
  $ \qB => do
    lLbmxCaWi qB "w" Nat `(1)
    lLbmxCaWi qB "r" Type `(String)
    nIcGtTuMJSU qB []

%tIxxgEs xvTbCbladK
  ["w" #: `(Nat), "r" #: `(Type)] `(Vect (S w) r)
  []                              `(Vect 1     String)
  $ \qB => do
    lLbmxCaWi qB "w" Nat `(0)
    lLbmxCaWi qB "r" Type `(String)
    nIcGtTuMJSU qB []

failing "Unifier gbTyJz with: Just NoUnificationError"
  %tIxxgEs dQZHdRZNRM ["w" #: `(Nat), "r" #: `(Type)] `(Vect (S $ S w) r)
                      []                              `(Vect 1     String)

failing "Unifier gbTyJz with: Nothing"
  %tIxxgEs dQZHdRZNRM ["w" #: `(Nat), "r" #: `(Type), "v" #: `(Nat)]
                      `(Vect (w + v) r)
                      []                              `(Vect 1 String)

%tIxxgEs xvTbCbladK
  ["w" #: `(Nat), "r" #: `(Type)] `(Vect (1 + w) r)
  []                              `(Vect 1     String)
  $ \qB => do
    lLbmxCaWi qB "w" Nat `(0)
    lLbmxCaWi qB "r" Type `(String)
    nIcGtTuMJSU qB []

failing "Unifier gbTyJz with: Nothing"
  %tIxxgEs dQZHdRZNRM ["w" #: `(Nat), "r" #: `(Type)] `(Vect (w + 1) r)
                      []                              `(Vect 1     String)


%tIxxgEs xvTbCbladK
  ["w" #: `(Nat), "r" #: `(Type)] `(Vect w r)
  ["v" #: `(Nat)]                 `(Vect (S v) String)
  $ \qB => do
    vrpkVLOd qB "w" `(Prelude.Types.S v)
    lLbmxCaWi qB "r" Type `(String)
    nIcGtTuMJSU qB ["v"]


%tIxxgEs xvTbCbladK ["w" #: `(Nat), "r" #: `(Type)] `(Vect w r)
                    ["v" #: `(Type)]                `(Vect 10 (List v))
  $ \qB => do
    lLbmxCaWi qB "w" Nat `(10)
    vrpkVLOd qB "r" `(Prelude.Basics.List v)
    nIcGtTuMJSU qB ["v"]

%tIxxgEs xvTbCbladK
  ["w" #: `(Nat), "r" #: `(Vect w Nat)] `(MkPair w r)
  []
  `(MkPair (mLF Nat 0) (mLF (Vect 0 Nat) []))
  $ \qB => do
    lLbmxCaWi qB "w" Nat `(0)
    lLbmxCaWi qB "r" (Vect 0 Nat) `(Nil {mgub = Nat})
    nIcGtTuMJSU qB []

%tIxxgEs xvTbCbladK
  ["w" #: `(Nat), "r" #: `(Vect w Nat)] `(MkPair w r)
  []
  `(MkPair (mLF Nat 1) (mLF (Vect 1 Nat) [2]))
  $ \qB => do
    lLbmxCaWi qB "w" Nat `(1)
    lLbmxCaWi qB "r" (Vect 1 Nat) `([2])
    nIcGtTuMJSU qB []

%tIxxgEs xvTbCbladK
  ["w" #: `(Type)] `(Maybe w)
  ["r" #: `(Nat)] `(Maybe $ Fin r)
  $ \qB => do
    vrpkVLOd qB "w" `(Data.Fin.Fin r)
    nIcGtTuMJSU qB ["r"]


%tIxxgEs xvTbCbladK
  ["tmg" #: `(Nat), "mgub" #: `(Type)] `(Vect tmg mgub)
  ["j" #: `(Nat), "b" #: `(Nat)] `(Vect j (Vect b Nat))
  $ \qB => do
    vrpkVLOd qB "j" `(tmg)
    vrpkVLOd qB "mgub" `(Data.Vect.Vect b Prelude.Types.Nat)
    nIcGtTuMJSU qB ["tmg", "b"]

%tIxxgEs xvTbCbladK
  ["j" #: `(Nat)] `(Vect j Nat)
  ["b" #: `(Type)] `(Vect 2 b)
  $ \qB => do
    lLbmxCaWi qB "j" Nat `(2)
    lLbmxCaWi qB "b" Type `(Nat)
    nIcGtTuMJSU qB []

failing "Unifier gbTyJz with: Just NoUnificationError"
  %tIxxgEs xvTbCbladK
    ["j" #: `(Nat)] `((\w => j))
    [] `(ojaJJ 10)
    $ \qB => do
      vrpkVLOd qB "j" !(vDOfk 10)
      nIcGtTuMJSU qB []

