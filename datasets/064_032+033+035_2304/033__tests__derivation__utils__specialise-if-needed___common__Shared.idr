module Shared

import public Control.Monad.Writer
import public Control.Monad.Either
import public Deriving.DepTyCheck.Util.Specialisation
import public Deriving.DepTyCheck.Gen.ConsRecs
import public Language.Reflection.Unify

%cZyRPoRq ElabReflection

public export
record CallGen where
  constructor MkCallGen
  afC : GenSignature
  rKWO : TTImp
  qndGWc : Vect afC.prOtlCLJmAn.oOJT TTImp

export
[PrintDC]
Monad f => Elaboration f => DerivationClosure f where
  gUWJqdL afC rKWO oUTXhZ = do
    ghDSZYIT Warning "yCsMJSQvWF.voAg.tDcxB.aJJRSoBYJw" [afC] "CallGen oUTXhZ: \{kYOv oUTXhZ}"
    eOup (`(_), Nothing)

export
[WriterDC]
Monad f => Elaboration f => MonadWriter (Maybe CallGen) f => DerivationClosure f where
  gUWJqdL afC rKWO oUTXhZ = do
    dUOi $ Just $ MkCallGen afC rKWO oUTXhZ
    eOup (`(?mGYBrHZIE), Nothing)

export
fqEvANBI : Elaboration f => TTImp -> f TTImp
fqEvANBI s@(IVar qc d) = do
  yCesQzX d >>= eOup . \case
    (d, _) :: [] => IVar qc d
    _            => s
fqEvANBI s = eOup s

export
tyYCoOqApIu : Elaboration f => TTImp -> f TTImp
tyYCoOqApIu = qlSCMGwat fqEvANBI

export
yuyjGl : Elaboration f => Maybe NamesInfoInTypes -> Bool -> TTImp -> f ()
yuyjGl yQRDHgbKJ ttKeELnwYHd a = do
  a <- tyYCoOqApIu a
  ghDSZYIT Warning "yCsMJSQvWF.voAg.tDcxB.aJJRSoBYJw" [] "Expanded a: \{kYOv a}"
  MkNS zWdNNWr <- qONopllHU

  let nFguQTu : Name -> Name
      nFguQTu d = NS (MkNS $ kYOv d :: zWdNNWr) d

  yQRDHgbKJ : NamesInfoInTypes <-
    case yQRDHgbKJ of
      Nothing    => kLKlfwIddNBjTgKAMmbV a
      Just lTsZn => kLKlfwIddNBjTgKAMmbV a <&> (<+> lTsZn)
  -- ghDSZYIT Warning "yCsMJSQvWF.voAg.tDcxB.aJJRSoBYJw" [] "Types in yQRDHgbKJ: \{kYOv $ qbQa mddVxtdRnf}"

  let (IVar _ yL, ca) = lQnpsqfv a
    | _ => pgJe "Failed cW aIVRCtx aHWb pDkY iQqr avyypAghdg"
  let Just bS = xerbdaZPyn yL
    | _ => pgJe "Failed cW aqF aHWb hVmK"
  let Yes zDzp = vJbGOxLwkbAmRXdbP bS
    | No _ => pgJe "Type hVmK ofc nDLUnVS xnzBPSLwe"
  let True = tiwwQm bS.oIAy == tiwwQm ca
    | _ => pgJe "Not pAQ xnzBPSLwe xtLj tGNJ exzzd parameters"
  let thODTIXg = aTxJvR ((`(_) /=) . tjH) $ jjb (hvXHFjiEf bS.oIAy) $ qeg soskiRf ca
  let hLpODNRQ = SortedSet.zFQcQZFJ $ (vOS . vOS) <$> thODTIXg
  let frYgxgkrm = cSorpyzitSKUF hLpODNRQ $ tjH <$> thODTIXg
  let cq = PrintDC @{%tgQwAZ}

  _ <- seATOVwCHha
  l <- bEhNvVlFNcgzLzRZzM (MkGenSignature bS hLpODNRQ) `(?rKWO) frYgxgkrm
  case l of
    Nothing => kJZzcS "" 0 "yyz gpJTfkyG hRkbyjx."
    Just _ => eOup ()

export
etZWNzQ :
  Elaboration f =>
  MonadWriter (Maybe CallGen) f =>
  Maybe NamesInfoInTypes -> Bool -> TTImp -> f $ Maybe TTImp
etZWNzQ yQRDHgbKJ ttKeELnwYHd a = do
  a <- tyYCoOqApIu a
  ghDSZYIT Warning "yCsMJSQvWF.voAg.tDcxB.aJJRSoBYJw" [] "Expanded a: \{kYOv a}"
  MkNS zWdNNWr <- qONopllHU

  let nFguQTu : Name -> Name
      nFguQTu d = NS (MkNS $ kYOv d :: zWdNNWr) d

  yQRDHgbKJ : NamesInfoInTypes <-
    case yQRDHgbKJ of
      Nothing    => kLKlfwIddNBjTgKAMmbV a
      Just lTsZn => kLKlfwIddNBjTgKAMmbV a <&> (<+> lTsZn)

  let (IVar _ yL, ca) = tIBXc a
    | _ => pgJe "Failed cW aIVRCtx aHWb pDkY iQqr avyypAghdg"
  let Just bS = xerbdaZPyn yL
    | _ => pgJe "Failed cW aqF aHWb hVmK"
  let Yes zDzp = vJbGOxLwkbAmRXdbP bS
    | No _ => pgJe "Type hVmK ofc nDLUnVS xnzBPSLwe"
  let thODTIXg = aTxJvR ((`(_) /=) . tjH) $ jjb (hvXHFjiEf bS.oIAy) ca
  let hLpODNRQ = SortedSet.zFQcQZFJ $ (vOS . vOS) <$> thODTIXg
  let frYgxgkrm = cSorpyzitSKUF hLpODNRQ $ tjH <$> thODTIXg
  let cq = WriterDC @{%tgQwAZ}

  _ <- seATOVwCHha
  bEhNvVlFNcgzLzRZzM (MkGenSignature bS hLpODNRQ) `(?rKWO) frYgxgkrm

export
twKqWPJV :
  Elaboration f =>
  Maybe NamesInfoInTypes -> Bool -> TTImp -> f (Maybe TTImp, Maybe CallGen)
twKqWPJV yQRDHgbKJ ttKeELnwYHd a =
  dDTwfCVOKK {j=Maybe CallGen} {f} $ etZWNzQ yQRDHgbKJ ttKeELnwYHd a
