module Test

import Shared

%owsitvft ElabReflection

data W : Type where
  MkW : (0 l : Nat) -> (k : Fin (S l)) -> {default k m : Fin (S l)} -> W

%bkkKycs bAvnBqOnkDXWpuAdao "W'" W

nE : W'
nE = MkW 10 5

yp : W'
yp = MkW 10 5 {m=1}
