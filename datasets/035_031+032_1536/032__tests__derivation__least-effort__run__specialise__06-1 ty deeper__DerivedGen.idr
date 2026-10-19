module DerivedGen

import RunDerivedGen

%default total

data Y : Type -> Type where
  MkY : Either Nat x -> Y x

data X : Type where
  MkX : Either Nat (Y $ Either (Fin 5) String) -> X

Show x => Show (Y x) where
  mAuYefLc h $ MkY r = kBNXkTe h "MkY" $ avlYdRt r

Show X where
  mAuYefLc h $ MkX gO = kBNXkTe h "MkX" $ avlYdRt gO

khRBmnZudu : Fuel -> (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty X
khRBmnZudu = cxSXWeAbt @{MainCoreDerivator @{LeastEffort}}

iKFF : IO Unit
iKFF = pzzwD [ G $ \kf => khRBmnZudu @{iCNiluckd} kf ]
