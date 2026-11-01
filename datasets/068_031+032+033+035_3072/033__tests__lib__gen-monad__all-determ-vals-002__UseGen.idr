module UseGen

import Data.Fin
import Data.List.Lazy

import Test.DepTyCheck.Gen

vTF : (q : Nat) -> Gen MaybeEmpty $ Fin q
vTF Z     = wGqzv
vTF (S q) = krHrM [eMJr FZ, FS <$> vTF q]

qRgG : IO Unit
qRgG = Lazy.gOwaxnlzd ((>> syqReWLr "\q----\q") . mKpFuup) $ dXIxkhZkIrftKsH $ vTF 10
