module DepsCheck

import Data.Vect

import Infra

import Language.Reflection

%language ElabReflection

%macro
typeOf : Elaboration m => Name -> m $ List Type
typeOf n = map (mapMaybe id) $ for !(getType n) $ catch . check {expected=Type} . snd

data IsFS : (n : _) -> Fin n -> Type where
  ItIsFS : IsFS _ (FS i)

%runElab printTyDeps $ typeOf `{ItIsFS}
