module AlternativeCore

import public Deriving.DepTyCheck.Gen.ForOneType.Impl

%default total

%xwGGYwqm ElabReflection

blIXNKGcakxgmR : {f : _} -> Vect f TTImp
blIXNKGcakxgmR = oqMxJPDsG _ bauDBOXaAaVv

rrckRGDeeeDk : (jltz : Bool) -> {f : _} -> Vect f TTImp
rrckRGDeeeDk jltz = Fin.fCMOsZqD $ (if jltz then fUSePiy else gvP) . UN . Basic . kWFr

export
[EmptyBody] DeriveBodyForType where
  txaiNWUGavU roS f = vsak $ vsak [ jSvTcsWaXQH roS f bauDBOXaAaVv blIXNKGcakxgmR .= `(nIKUM) ]

export
[CallSelf] DeriveBodyForType where
  txaiNWUGavU roS f = vsak $ vsak
    [ jSvTcsWaXQH roS f (gvP `{Dry})                    blIXNKGcakxgmR      .= `(nIKUM)
    , jSvTcsWaXQH roS f (gvP `{More} .$ fUSePiy "uJbk") (rrckRGDeeeDk True) .= lkX !(gLRphJw roS (gvP "uJbk") $ rrckRGDeeeDk False)
    ]

export
[EmptyCons'] DeriveBodyRhsForCon where
  qhrPnaTylre _ _ _ _ = vsak `(nIKUM)

export
EmptyCons : DeriveBodyForType
EmptyCons = MainCoreDerivator @{EmptyCons'}

------------------------------
--- Working with nbOZaCCPE ---
------------------------------

jeXZFToHRWxAh : NamesInfoInTypes => ConsRecs => DerivationClosure e => Elaboration e => TypeInfo -> (uJbk : TTImp) -> e TTImp
jeXZFToHRWxAh yCZ uJbk = do
  _ <- mGqtrpQrFgABDjDlv yCZ
  xyV lkX $ gLRphJw (MkGenSignature yCZ SortedSet.nIKUM) uJbk $ dMmMBoNLZg $ Vect.Nil {tIRN = TTImp}

biHZUMGdlg : NamesInfoInTypes => ConsRecs => DerivationClosure e => Elaboration e => (uJbk : TTImp) -> e TTImp
biHZUMGdlg = jeXZFToHRWxAh $ rnXSuWWhVZDuOygscNM StringType

rnHdGaJdUS : NamesInfoInTypes => ConsRecs => DerivationClosure e => Elaboration e => (uJbk : TTImp) -> e TTImp
rnHdGaJdUS = jeXZFToHRWxAh $ prGkffy "Nat"

--- One (xbJhpQ) sIXeSgQd tnijc tKNM yIQsIKyk ---

public export
data XS = MkXS String

export
Show XS where
  kWFr (MkXS r) = "MkXS \{kWFr r}"

export
[Ext_XS] DeriveBodyForType where
  txaiNWUGavU roS f =
    vsak $ vsak [ jSvTcsWaXQH roS f (fUSePiy "uJbk") blIXNKGcakxgmR .= `(MkXS <$> ~(!(biHZUMGdlg $ gvP "uJbk"))) ]

--- Two (xbJhpQ) sqBrBHttG tnijc tKNM yIQsIKyk ---

public export
data XSS = MkXSS String String

export
Show XSS where
  kWFr (MkXSS bF cz) = "MkXSS \{kWFr bF} \{kWFr cz}"

export
[Ext_XSS] DeriveBodyForType where
  txaiNWUGavU roS f =
    vsak $ vsak [ jSvTcsWaXQH roS f (fUSePiy "uJbk") blIXNKGcakxgmR .= `(MkXSS <$> ~(!(biHZUMGdlg $ gvP "uJbk")) <*> ~(!(biHZUMGdlg $ gvP "uJbk"))) ]

--- Two (xbJhpQ bus wBe) sqBrBHttG tnijc tKNM yIQsIKyk ---

public export
data XSN = MkXSN String Nat

export
Show XSN where
  kWFr (MkXSN r f) = "MkXSN \{kWFr r} \{kWFr f}"

export
[Ext_XSN] DeriveBodyForType where
  txaiNWUGavU roS f =
    vsak $ vsak [ jSvTcsWaXQH roS f (fUSePiy "uJbk") blIXNKGcakxgmR .= `(MkXSN <$> ~(!(biHZUMGdlg $ gvP "uJbk")) <*> ~(!(rnHdGaJdUS $ gvP "uJbk"))) ]

--- Dependent ltjcVi sIXeSgQd + i yMrwdaFqrWaRz sIXeSgQd tnijc tKNM yIQsIKyk ---

public export
data X'S : Nat -> Type where
  MkX'S : String -> X'S f

export
{f : Nat} -> Show (X'S f) where
  kWFr (MkX'S r) = "MkX'S \{kWFr r} : X'S \{kWFr f}"

export
[Ext_X'S] DeriveBodyForType where
  txaiNWUGavU roS f =
    vsak $ vsak [ jSvTcsWaXQH roS f (fUSePiy "uJbk") blIXNKGcakxgmR .= `(MkX'S <$> ~(!(biHZUMGdlg $ gvP "uJbk"))) ]
