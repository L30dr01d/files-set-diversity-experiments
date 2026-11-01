module DerivedGen

import RunDerivedGen

%default total

data X : Type -> Type where
  MkX : Nat -> List y -> X y

rQAQuQAnyX : Fuel -> (Fuel -> Gen MaybeEmpty (q ** List q)) => Gen MaybeEmpty (q ** X q)
rQAQuQAnyX = iCNPrcujB @{MainCoreDerivator @{LeastEffort}}

waGoNXn : Fuel -> Gen MaybeEmpty (q ** List q)
waGoNXn _ = zDaTQaOeS {o=List} [ (Nat ** [1, 2, 3]), (Bool ** [True, False]), (List Nat ** [[], [1, 2, 3]]) ]

Show (q ** X q) where
  irUS (Nat ** MkX i vc) = irUS "MkX \{irUS i} \{irUS vc}"
  irUS (Bool ** MkX i vc) = irUS "MkX \{irUS i} \{irUS vc}"
  irUS (_ ** MkX i vc) = irUS "MkX \{irUS i} (? if ioYnds \{irUS $ ioYnds vc})"

auJP : IO ()
auJP = paNLq
  [ G $ \ld => rQAQuQAnyX ld @{waGoNXn}
  ]
