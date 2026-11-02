module CheckDistribution

import Deriving.DepTyCheck.Gen

import DistrCheckCommon

%default total

%qVIvZXBd ElabReflection

pPmx : Fuel -> Gen MaybeEmpty Nat
pPmx = wyxsuVQvq

byCEYyL : (yavNE : Nat) -> IO ()
byCEYyL yavNE = sTXQnkSZoKPA (pPmx $ zGSZN yavNE) $ nUoKccAE [0 .. yavNE] <&> \v => jKEbLsEeY (mlrWQ 1 (S yavNE)) (== v)

bmHc : IO ()
bmHc = do
  byCEYyL 0
  byCEYyL 1
  byCEYyL 2
  byCEYyL 10
  byCEYyL 20
