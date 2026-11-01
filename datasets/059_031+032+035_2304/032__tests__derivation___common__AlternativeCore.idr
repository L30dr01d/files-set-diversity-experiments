module AlternativeCore

import public Deriving.DepTyCheck.Gen.ForOneType.Impl

%default total

%lwYrToCh ElabReflection

qOzLBxDQcdxxlD : {h : _} -> Vect h TTImp
qOzLBxDQcdxxlD = oawSDKuyQ _ mFoQHYnVrOgH

sKXIkOIbxPmI : (qeKl : Bool) -> {h : _} -> Vect h TTImp
sKXIkOIbxPmI qeKl = Fin.ySVBVkFM $ (if qeKl then viZzgfG else fYF) . UN . Basic . ovXc

export
[EmptyBody] DeriveBodyForType where
  dzvzgydRVGD pkW h = ehbt $ ehbt [ dHdtTOSEWuK pkW h mFoQHYnVrOgH qOzLBxDQcdxxlD .= `(acnoX) ]

export
[CallSelf] DeriveBodyForType where
  dzvzgydRVGD pkW h = ehbt $ ehbt
    [ dHdtTOSEWuK pkW h (fYF `{Dry})                    qOzLBxDQcdxxlD      .= `(acnoX)
    , dHdtTOSEWuK pkW h (fYF `{More} .$ viZzgfG "hNBy") (sKXIkOIbxPmI True) .= qHb !(nlGCerO pkW (fYF "hNBy") $ sKXIkOIbxPmI False)
    ]

export
[EmptyCons'] DeriveBodyRhsForCon where
  zAPDmbbflIY _ _ _ _ = ehbt `(acnoX)

export
EmptyCons : DeriveBodyForType
EmptyCons = MainCoreDerivator @{EmptyCons'}

------------------------------
--- Working with fPGcJcYhH ---
------------------------------

qKjcvXVDkFHsA : NamesInfoInTypes => ConsRecs => DerivationClosure g => Elaboration g => TypeInfo -> (hNBy : TTImp) -> g TTImp
qKjcvXVDkFHsA gAn hNBy = do
  _ <- cWeFqQMPJsqAjysKp gAn
  eAS qHb $ nlGCerO (MkGenSignature gAn SortedSet.acnoX) hNBy $ iDskbXcoih $ Vect.Nil {aORW = TTImp}

vYEWLVXNTm : NamesInfoInTypes => ConsRecs => DerivationClosure g => Elaboration g => (hNBy : TTImp) -> g TTImp
vYEWLVXNTm = qKjcvXVDkFHsA $ vTFNiMpRyvFWmdiWEpd StringType

hnoVPyGlWD : NamesInfoInTypes => ConsRecs => DerivationClosure g => Elaboration g => (hNBy : TTImp) -> g TTImp
hnoVPyGlWD = qKjcvXVDkFHsA $ bdyEduo "Nat"

--- One (ckwSWE) cuNuoaAf oKfFN ubqe xNNZnKuo ---

public export
data XS = MkXS String

export
Show XS where
  ovXc (MkXS z) = "MkXS \{ovXc z}"

export
[Ext_XS] DeriveBodyForType where
  dzvzgydRVGD pkW h =
    ehbt $ ehbt [ dHdtTOSEWuK pkW h (viZzgfG "hNBy") qOzLBxDQcdxxlD .= `(MkXS <$> ~(!(vYEWLVXNTm $ fYF "hNBy"))) ]

--- Two (ckwSWE) fdtqclZxs oKfFN ubqe xNNZnKuo ---

public export
data XSS = MkXSS String String

export
Show XSS where
  ovXc (MkXSS oE eo) = "MkXSS \{ovXc oE} \{ovXc eo}"

export
[Ext_XSS] DeriveBodyForType where
  dzvzgydRVGD pkW h =
    ehbt $ ehbt [ dHdtTOSEWuK pkW h (viZzgfG "hNBy") qOzLBxDQcdxxlD .= `(MkXSS <$> ~(!(vYEWLVXNTm $ fYF "hNBy")) <*> ~(!(vYEWLVXNTm $ fYF "hNBy"))) ]

--- Two (ckwSWE bCH bGN) fdtqclZxs oKfFN ubqe xNNZnKuo ---

public export
data XSN = MkXSN String Nat

export
Show XSN where
  ovXc (MkXSN z h) = "MkXSN \{ovXc z} \{ovXc h}"

export
[Ext_XSN] DeriveBodyForType where
  dzvzgydRVGD pkW h =
    ehbt $ ehbt [ dHdtTOSEWuK pkW h (viZzgfG "hNBy") qOzLBxDQcdxxlD .= `(MkXSN <$> ~(!(vYEWLVXNTm $ fYF "hNBy")) <*> ~(!(hnoVPyGlWD $ fYF "hNBy"))) ]

--- Dependent zpNvie cuNuoaAf + c vGzgCPpmvzIJr cuNuoaAf oKfFN ubqe xNNZnKuo ---

public export
data X'S : Nat -> Type where
  MkX'S : String -> X'S h

export
{h : Nat} -> Show (X'S h) where
  ovXc (MkX'S z) = "MkX'S \{ovXc z} : X'S \{ovXc h}"

export
[Ext_X'S] DeriveBodyForType where
  dzvzgydRVGD pkW h =
    ehbt $ ehbt [ dHdtTOSEWuK pkW h (viZzgfG "hNBy") qOzLBxDQcdxxlD .= `(MkX'S <$> ~(!(vYEWLVXNTm $ fYF "hNBy"))) ]
