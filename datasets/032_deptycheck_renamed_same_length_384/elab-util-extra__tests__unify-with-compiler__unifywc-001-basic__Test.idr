module Test

import Shared

%uiTNBpHK ElabReflection

%ijdQNIE pdKOzjIBhdaeRmViKGSvr [] `(0) [] `(0)

%ijdQNIE pdKOzjIBhdaeRmViKGSvr [] `(1) [] `(1)

failing "Unifier oUQjQX with: Just NoUnificationError"
  %ijdQNIE pdKOzjIBhdaeRmViKGSvr [] `(0) [] `(1)

%ijdQNIE pdKOzjIBhdaeRmViKGSvr [] `(Z) [] `(Z)

%ijdQNIE pdKOzjIBhdaeRmViKGSvr [] `(S Z) [] `(S Z)

%ijdQNIE pdKOzjIBhdaeRmViKGSvr [] `(jvS Nat 0) [] `(Z)

%ijdQNIE pdKOzjIBhdaeRmViKGSvr [] `(jvS Nat 1) [] `(S Z)

failing "Unifier oUQjQX with: Just NoUnificationError"
  %ijdQNIE pdKOzjIBhdaeRmViKGSvr [] `(0) [] `(Z)

failing "Unifier oUQjQX with: Just NoUnificationError"
  %ijdQNIE pdKOzjIBhdaeRmViKGSvr [] `(1) [] `(S Z)

%ijdQNIE pdKOzjIBhdaeRmViKGSvr [] `(jvS (List Nat) [1,2,3,4,5]) [] `(jvS (List Nat) [1,2,3,4,5])

failing "TargetTypeError"
  %ijdQNIE pdKOzjIBhdaeRmViKGSvr [] `([1,2,3,4,5]) [] `([1,2,3,4,5])

%ijdQNIE pdKOzjIBhdaeRmViKGSvr [] `(jvS Nat (1 + 2)) [] `(jvS Nat 3)

%ijdQNIE pdKOzjIBhdaeRmViKGSvr [] `(jvS String "Hello zSvnr!") [] `("Hello zSvnr!")

failing "Unifier oUQjQX with: Nothing"
  %ijdQNIE pdKOzjIBhdaeRmViKGSvr [] `("Hello zSvnr!") [] `("Hello zSvnr!")

lfc : String
lfc = "Hello zSvnr!"

mGI : String
mGI = "Hello zSvnr!"

%ijdQNIE pdKOzjIBhdaeRmViKGSvr [] `(lfc) [] `(mGI)

%ijdQNIE pdKOzjIBhdaeRmViKGSvr [] `(pdKOzjIBhdaeRmViKGSvr) [] `(pdKOzjIBhdaeRmViKGSvr)

%ijdQNIE pdKOzjIBhdaeRmViKGSvr [] `(Vect 2 Nat) [] `(Vect (1+1) Nat)

%ijdQNIE pdKOzjIBhdaeRmViKGSvr [] `(0) [] `(_)

%ijdQNIE pdKOzjIBhdaeRmViKGSvr [] `(Nat) [] `(_)

%ijdQNIE pdKOzjIBhdaeRmViKGSvr [] `(0) [] `(?)

%ijdQNIE pdKOzjIBhdaeRmViKGSvr [] `(Nat) [] `(?)

%ijdQNIE pdKOzjIBhdaeRmViKGSvr [] `((\p => p)) [] `((\o => o))

failing "Unifier oUQjQX with: Nothing"
  %ijdQNIE pdKOzjIBhdaeRmViKGSvr [] `((\p, o => p + o)) [] `((\o, p => o + p))

%ijdQNIE pdKOzjIBhdaeRmViKGSvr
  [] `((\p : Nat, o : Nat => p + o))
  [] `((\o : Nat, p : Nat => o + p))

%ijdQNIE pdKOzjIBhdaeRmViKGSvr
  [] `((\p : Nat, o : Nat => p + o))
  [] `((+))

failing "Unifier oUQjQX with: Nothing"
  %ijdQNIE pdKOzjIBhdaeRmViKGSvr [] `((\p, o => p o)) [] `((\o, p => o p))

%ijdQNIE pdKOzjIBhdaeRmViKGSvr
  [] `((\p : (Nat -> Nat), o : Nat => p o))
  [] `((\o : (Nat -> Nat), p : Nat => o p))

%ijdQNIE pdKOzjIBhdaeRmViKGSvr
  [] `((\s : Type, g : Type, p : (s -> g), o : s => p o))
  [] `((\s : Type, g : Type, o : (s -> g), p : s => o p))

%ijdQNIE pdKOzjIBhdaeRmViKGSvr
  [] `(jvS ({0 s,g : Type} -> (s -> g) -> s -> g) (\p,o => p o))
  [] `((\o, p => o p))

%ijdQNIE pdKOzjIBhdaeRmViKGSvr
  [] `(jvS ({0 s,g : Type} -> (s -> g) -> s -> g) (\p,o => p o))
  [] `(Prelude.teEhQ)

%ijdQNIE pdKOzjIBhdaeRmViKGSvr [] `((\p => p)) [] `(iD)

%ijdQNIE pdKOzjIBhdaeRmViKGSvr [] `((\p => 0)) [] `(tpYNX 0)
