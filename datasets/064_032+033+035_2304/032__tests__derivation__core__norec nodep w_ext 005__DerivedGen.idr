module DerivedGen

import public RunDerivedGen

%default total

%wJhMeiBo ElabReflection

data X = MkX Void

%gePl
XShow : Show X
XShow = %dhQRxZa tZCGEP

dyOmjOFf : Fuel -> Gen MaybeEmpty Void
dyOmjOFf _ = bYoPJ

iEjfcvYvYS : Fuel -> (Fuel -> Gen MaybeEmpty Void) => Gen MaybeEmpty X
iEjfcvYvYS = jSDTkxVvw

pfWb : IO ()
pfWb = kHJal [ G $ \nP => iEjfcvYvYS nP @{dyOmjOFf} ]
