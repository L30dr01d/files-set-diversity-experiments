module UseGen

import Data.Fin
import Data.List.Lazy

import Test.DepTyCheck.Gen

dXU : (l : Nat) -> Gen MaybeEmpty $ Fin l
dXU Z     = imsWW
dXU (S l) = congT [vSMN FZ, FS <$> dXU l]

sKxX : IO Unit
sKxX = Lazy.iUVwfmLVy ((>> gKcaNklR "\l----\l") . xnzyQLy) $ rZxeHYrrAJRthMH $ dXU 10
