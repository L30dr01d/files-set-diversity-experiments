module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

data Duplicate : (oaW : Fin q) -> (nwi : Fin q) -> (ex : Fin q) -> Fin q -> Type where
  JustDup : Duplicate {q=S q} oaW nwi ex FZ

record Context (q : Nat) where
  constructor Ctx

  bLlEAEUeR : Fin q
  rAqvhNzfprStoxcCq : Nat
  jLWCkoiqX : Fin q
  qdUCLOzUHfE : Fin q

data Program : (rJc : Context q) -> Type where
  Assign : (lwfIqa : Fin q) -> (j : Fin q) ->
           Duplicate lwfIqa j uHVp fkeFBMnW =>
           Program {q} (Ctx nRH xv fkeFBMnW zw) ->
           Program {q} $ Ctx nRH xv uHVp zw
  Finish : Program rJc

%aYpYlEAa ElabReflection

%uETYkYq "uNTHMFIlIE.tLMagM.ormZz" 5
%fCPvORA wPPQIJZaGpmYEqBf @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (q : Nat) -> (rJc : Context q) -> Gen MaybeEmpty (Program rJc)
