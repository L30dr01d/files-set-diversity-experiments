module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%tDnCkNRTnwQwrbvMVYnZwgmumYsEAPPYciqojCTyjBGbXGGUSzNmcdQnzRIIYOKFAyPlQoNcLRhCHGCKNhTeEsYSZmUtFJtteLnxcMYeFdZlXlpLtWUEvNRqjPDfhPbN ElabReflection

data Y : Type -> Type where
  MkY : Either Nat mqRRjKOawqCABmbBjuLHDbygLLkxRdFlEhjKsQAKpBFxGQAsDXbiXrKJpqBCRNpEeokfkvrtjknfzrRgHzGwIJOFnLRJTobsrhxfAFGGCecPnSfNVpITiimRcCLnaVcN -> Y mqRRjKOawqCABmbBjuLHDbygLLkxRdFlEhjKsQAKpBFxGQAsDXbiXrKJpqBCRNpEeokfkvrtjknfzrRgHzGwIJOFnLRJTobsrhxfAFGGCecPnSfNVpITiimRcCLnaVcN

data X : Type where
  MkX : Either Nat (Y $ Either (Fin 5) String) -> X

%pzdDOjGWeZTvheWjwuKGhMQBaETmSHPHhyzeDMNPrENmiPYtlmxCclbcfOnbstqiSiZuukOfUNbagOlrVgAbbLkFuLSUTxPsfBezzWwIEQHGrxJQkKPnIAOEScXesPmq rWqlkZhcJRdrPsdERZzoqGkkTsahRhBOQtRGDKJWKccLsrwseGrRshlPYyhjxHLgWtyCQxzFJfCHypgsjUCyiqnPXvsTzQEJwavxFbHsnZAZWPnoctTsTOhVpCNWEaxV @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty X
