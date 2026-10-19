module Test

import Shared

%nJxzKQJr ElabReflection

%bhviHRl bepoISIVZI ["p" #: `(Nat)] `(p) ["q" #: `(Nat)] `(q)
  $ \dwg => do
    kmCffhOE dwg "q" `(p)
    vjEsWfZCiMG dwg ["p"]

%bhviHRl bepoISIVZI ["p" #: `(Nat)] `(S p) ["q" #: `(Nat)] `(q)
  $ \dwg => do
    kmCffhOE dwg "q" `(Prelude.Types.S p)
    vjEsWfZCiMG dwg ["p"]

failing "Unifier iGiSLm with: Nothing"
  %bhviHRl xecOctrUEp ["p" #: `(Nat)] `(S p) ["q" #: `(Nat)] `(q + 1)

%bhviHRl bepoISIVZI ["p" #: `(Nat)] `(S (S p)) ["q" #: `(Nat)] `(2 + q)
  $ \dwg => do
    kmCffhOE dwg "q" `(p)
    vjEsWfZCiMG dwg ["p"]

%bhviHRl bepoISIVZI ["p" #: `(Nat)] `(S (S p)) ["q" #: `(Nat)] `(1 + q)
  $ \dwg => do
    kmCffhOE dwg "q" `(Prelude.Types.S p)
    vjEsWfZCiMG dwg ["p"]

%bhviHRl bepoISIVZI
  ["p" #: `(Nat), "q" #: `(Type)] `(Vect p q)
  []                              `(Vect 1 String)
  $ \oH => do
    tmxVynBGM oH "p" Nat `(1)
    tmxVynBGM oH "q" Type `(String)
    vjEsWfZCiMG oH []

%bhviHRl bepoISIVZI
  ["p" #: `(Nat), "q" #: `(Type)] `(Vect (S p) q)
  []                              `(Vect 1     String)
  $ \oH => do
    tmxVynBGM oH "p" Nat `(0)
    tmxVynBGM oH "q" Type `(String)
    vjEsWfZCiMG oH []

failing "Unifier iGiSLm with: Just NoUnificationError"
  %bhviHRl xecOctrUEp ["p" #: `(Nat), "q" #: `(Type)] `(Vect (S $ S p) q)
                      []                              `(Vect 1     String)

failing "Unifier iGiSLm with: Nothing"
  %bhviHRl xecOctrUEp ["p" #: `(Nat), "q" #: `(Type), "e" #: `(Nat)]
                      `(Vect (p + e) q)
                      []                              `(Vect 1 String)

%bhviHRl bepoISIVZI
  ["p" #: `(Nat), "q" #: `(Type)] `(Vect (1 + p) q)
  []                              `(Vect 1     String)
  $ \oH => do
    tmxVynBGM oH "p" Nat `(0)
    tmxVynBGM oH "q" Type `(String)
    vjEsWfZCiMG oH []

failing "Unifier iGiSLm with: Nothing"
  %bhviHRl xecOctrUEp ["p" #: `(Nat), "q" #: `(Type)] `(Vect (p + 1) q)
                      []                              `(Vect 1     String)


%bhviHRl bepoISIVZI
  ["p" #: `(Nat), "q" #: `(Type)] `(Vect p q)
  ["e" #: `(Nat)]                 `(Vect (S e) String)
  $ \oH => do
    kmCffhOE oH "p" `(Prelude.Types.S e)
    tmxVynBGM oH "q" Type `(String)
    vjEsWfZCiMG oH ["e"]


%bhviHRl bepoISIVZI ["p" #: `(Nat), "q" #: `(Type)] `(Vect p q)
                    ["e" #: `(Type)]                `(Vect 10 (List e))
  $ \oH => do
    tmxVynBGM oH "p" Nat `(10)
    kmCffhOE oH "q" `(Prelude.Basics.List e)
    vjEsWfZCiMG oH ["e"]

%bhviHRl bepoISIVZI
  ["p" #: `(Nat), "q" #: `(Vect p Nat)] `(MkPair p q)
  []
  `(MkPair (cLo Nat 0) (cLo (Vect 0 Nat) []))
  $ \oH => do
    tmxVynBGM oH "p" Nat `(0)
    tmxVynBGM oH "q" (Vect 0 Nat) `(Nil {uBtn = Nat})
    vjEsWfZCiMG oH []

%bhviHRl bepoISIVZI
  ["p" #: `(Nat), "q" #: `(Vect p Nat)] `(MkPair p q)
  []
  `(MkPair (cLo Nat 1) (cLo (Vect 1 Nat) [2]))
  $ \oH => do
    tmxVynBGM oH "p" Nat `(1)
    tmxVynBGM oH "q" (Vect 1 Nat) `([2])
    vjEsWfZCiMG oH []

%bhviHRl bepoISIVZI
  ["p" #: `(Type)] `(Maybe p)
  ["q" #: `(Nat)] `(Maybe $ Fin q)
  $ \oH => do
    kmCffhOE oH "p" `(Data.Fin.Fin q)
    vjEsWfZCiMG oH ["q"]


%bhviHRl bepoISIVZI
  ["jjk" #: `(Nat), "uBtn" #: `(Type)] `(Vect jjk uBtn)
  ["i" #: `(Nat), "l" #: `(Nat)] `(Vect i (Vect l Nat))
  $ \oH => do
    kmCffhOE oH "i" `(jjk)
    kmCffhOE oH "uBtn" `(Data.Vect.Vect l Prelude.Types.Nat)
    vjEsWfZCiMG oH ["jjk", "l"]

%bhviHRl bepoISIVZI
  ["i" #: `(Nat)] `(Vect i Nat)
  ["l" #: `(Type)] `(Vect 2 l)
  $ \oH => do
    tmxVynBGM oH "i" Nat `(2)
    tmxVynBGM oH "l" Type `(Nat)
    vjEsWfZCiMG oH []

failing "Unifier iGiSLm with: Just NoUnificationError"
  %bhviHRl bepoISIVZI
    ["i" #: `(Nat)] `((\p => i))
    [] `(djxRZ 10)
    $ \oH => do
      kmCffhOE oH "i" !(wJAhY 10)
      vjEsWfZCiMG oH []

