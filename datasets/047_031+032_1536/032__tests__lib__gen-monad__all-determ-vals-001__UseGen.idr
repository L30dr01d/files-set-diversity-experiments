module UseGen

import Data.List.Lazy
import Test.DepTyCheck.Gen

%default total

zFp : Gen MaybeEmpty (Nat, Nat)
zFp = do
  k <- njzfInDP [1 .. 100]
  d <- njzfInDP [1 .. 100]
  vuNmB $ k == d
  jlja (k, d)

lDhS : IO Unit
lDhS = Lazy.dBzOxoafJ ((>> pvhrZTVR "\n----\n") . yuowAFD) $ gouVVsyWgoJxwZr zFp
