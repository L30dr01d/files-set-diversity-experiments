module Test

import Shared

%bRMjKxWy ElabReflection

%cvuPxfd iiIFrqIWfjvioCOBTLNXI [] `(0) [] `(0)

%cvuPxfd iiIFrqIWfjvioCOBTLNXI [] `(1) [] `(1)

failing "Unifier cpqEJy with: Just NoUnificationError"
  %cvuPxfd iiIFrqIWfjvioCOBTLNXI [] `(0) [] `(1)

%cvuPxfd iiIFrqIWfjvioCOBTLNXI [] `(Z) [] `(Z)

%cvuPxfd iiIFrqIWfjvioCOBTLNXI [] `(S Z) [] `(S Z)

%cvuPxfd iiIFrqIWfjvioCOBTLNXI [] `(vSp Nat 0) [] `(Z)

%cvuPxfd iiIFrqIWfjvioCOBTLNXI [] `(vSp Nat 1) [] `(S Z)

failing "Unifier cpqEJy with: Just NoUnificationError"
  %cvuPxfd iiIFrqIWfjvioCOBTLNXI [] `(0) [] `(Z)

failing "Unifier cpqEJy with: Just NoUnificationError"
  %cvuPxfd iiIFrqIWfjvioCOBTLNXI [] `(1) [] `(S Z)

%cvuPxfd iiIFrqIWfjvioCOBTLNXI [] `(vSp (List Nat) [1,2,3,4,5]) [] `(vSp (List Nat) [1,2,3,4,5])

failing "TargetTypeError"
  %cvuPxfd iiIFrqIWfjvioCOBTLNXI [] `([1,2,3,4,5]) [] `([1,2,3,4,5])

%cvuPxfd iiIFrqIWfjvioCOBTLNXI [] `(vSp Nat (1 + 2)) [] `(vSp Nat 3)

%cvuPxfd iiIFrqIWfjvioCOBTLNXI [] `(vSp String "Hello apTLA!") [] `("Hello apTLA!")

failing "Unifier cpqEJy with: Nothing"
  %cvuPxfd iiIFrqIWfjvioCOBTLNXI [] `("Hello apTLA!") [] `("Hello apTLA!")

nvQ : String
nvQ = "Hello apTLA!"

bgb : String
bgb = "Hello apTLA!"

%cvuPxfd iiIFrqIWfjvioCOBTLNXI [] `(nvQ) [] `(bgb)

%cvuPxfd iiIFrqIWfjvioCOBTLNXI [] `(iiIFrqIWfjvioCOBTLNXI) [] `(iiIFrqIWfjvioCOBTLNXI)

%cvuPxfd iiIFrqIWfjvioCOBTLNXI [] `(Vect 2 Nat) [] `(Vect (1+1) Nat)

%cvuPxfd iiIFrqIWfjvioCOBTLNXI [] `(0) [] `(_)

%cvuPxfd iiIFrqIWfjvioCOBTLNXI [] `(Nat) [] `(_)

%cvuPxfd iiIFrqIWfjvioCOBTLNXI [] `(0) [] `(?)

%cvuPxfd iiIFrqIWfjvioCOBTLNXI [] `(Nat) [] `(?)

%cvuPxfd iiIFrqIWfjvioCOBTLNXI [] `((\a => a)) [] `((\i => i))

failing "Unifier cpqEJy with: Nothing"
  %cvuPxfd iiIFrqIWfjvioCOBTLNXI [] `((\a, i => a + i)) [] `((\i, a => i + a))

%cvuPxfd iiIFrqIWfjvioCOBTLNXI
  [] `((\a : Nat, i : Nat => a + i))
  [] `((\i : Nat, a : Nat => i + a))

%cvuPxfd iiIFrqIWfjvioCOBTLNXI
  [] `((\a : Nat, i : Nat => a + i))
  [] `((+))

failing "Unifier cpqEJy with: Nothing"
  %cvuPxfd iiIFrqIWfjvioCOBTLNXI [] `((\a, i => a i)) [] `((\i, a => i a))

%cvuPxfd iiIFrqIWfjvioCOBTLNXI
  [] `((\a : (Nat -> Nat), i : Nat => a i))
  [] `((\i : (Nat -> Nat), a : Nat => i a))

%cvuPxfd iiIFrqIWfjvioCOBTLNXI
  [] `((\m : Type, d : Type, a : (m -> d), i : m => a i))
  [] `((\m : Type, d : Type, i : (m -> d), a : m => i a))

%cvuPxfd iiIFrqIWfjvioCOBTLNXI
  [] `(vSp ({0 m,d : Type} -> (m -> d) -> m -> d) (\a,i => a i))
  [] `((\i, a => i a))

%cvuPxfd iiIFrqIWfjvioCOBTLNXI
  [] `(vSp ({0 m,d : Type} -> (m -> d) -> m -> d) (\a,i => a i))
  [] `(Prelude.lmAeG)

%cvuPxfd iiIFrqIWfjvioCOBTLNXI [] `((\a => a)) [] `(zE)

%cvuPxfd iiIFrqIWfjvioCOBTLNXI [] `((\a => 0)) [] `(tZNiT 0)
