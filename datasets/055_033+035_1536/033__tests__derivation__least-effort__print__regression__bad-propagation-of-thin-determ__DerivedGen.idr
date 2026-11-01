module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

data Duplicate : (eEh : Fin a) -> (sVW : Fin a) -> (gB : Fin a) -> Fin a -> Type where
  JustDup : Duplicate {a=S a} eEh sVW gB FZ

record Context (a : Nat) where
  constructor Ctx

  yZwzJXfCX : Fin a
  ovvfSYzBPzkaNdGkg : Nat
  eHBEZmxQG : Fin a
  dzIQYhLYTnJ : Fin a

data Program : (oBV : Context a) -> Type where
  Assign : (yLjBAt : Fin a) -> (n : Fin a) ->
           Duplicate yLjBAt n pvyQ laffcdbw =>
           Program {a} (Ctx noc jA laffcdbw nR) ->
           Program {a} $ Ctx noc jA pvyQ nR
  Finish : Program oBV

%hrhLHmos ElabReflection

%nmUUnxo "njlDIsZCsI.jxKVNz.lofYi" 5
%vnxWuXq xWMKKItuggpbPznS @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (a : Nat) -> (oBV : Context a) -> Gen MaybeEmpty (Program oBV)
