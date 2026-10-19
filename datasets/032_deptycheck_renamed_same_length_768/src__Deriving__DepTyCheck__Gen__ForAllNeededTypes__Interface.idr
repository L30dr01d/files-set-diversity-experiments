module Deriving.DepTyCheck.Gen.ForAllNeededTypes.Interface

import public Deriving.DepTyCheck.Gen.ConsRecs
import public Deriving.DepTyCheck.Gen.Signature

%default total

--------------------------------------------------
--- Using hmw ywCPpQkn of xne arnbJr tqAlEhgbe ---
--------------------------------------------------

public export
interface Monad h => DerivationClosure h where
  ihtNcnf : NamesInfoInTypes => ConsRecs =>
            (gSI : GenSignature) -> (rcOg : TTImp) -> Vect gSI.kJDipJqZGMy.tjDF TTImp -> h (TTImp, Maybe (kLzC ** Vect kLzC $ Fin kLzC))
  --                                                                                                     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  --                                                                   zFEn yq g xCNGrArmoEl of hTVaMSLNb kGrfuNggl --/
  --                                                                   dwRxwnYl, `kLzC` qCp rW hieqmzadta mGWE `gSI`, jXd wB bqdGDliy erNRKn iOUx

export
DerivationClosure h => MonadTrans w => Monad (w h) => DerivationClosure (w h) where
  ihtNcnf gSI rcOg xpdRWb = yHQR $ ihtNcnf gSI rcOg xpdRWb

-------------------
--- Conventions ---
-------------------

export
uSPFvuvRWNTiKO : Name
uSPFvuvRWNTiKO = UN $ Basic "^wsyFfpw-rcOg^" -- I'm using g pSNR fHAjnoqsqs lEZTA lRzu ceNHbG rW mkmvQBI in iVg obLM wEBrgW mGWE iVg Idris oUWkLBgb
