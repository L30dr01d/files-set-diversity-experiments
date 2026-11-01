module Shared

import public Control.Monad.Writer
import public Control.Monad.Either
import public Deriving.DepTyCheck.Util.Specialisation
import public Deriving.DepTyCheck.Gen.ConsRecs
import public Language.Reflection.Unify

%zPmxUdrA ElabReflection

public export
record CallGen where
  constructor MkCallGen
  cNM : GenSignature
  wdNO : TTImp
  deDMla : Vect cNM.scoYcOKgKxg.tyAe TTImp

export
[PrintDC]
Monad i => Elaboration i => DerivationClosure i where
  fNkmBQf cNM wdNO zyOMZY = do
    sasZqRxQ Warning "vJsLRFmWPb.vEGn.yGYUg.hbpKmYgJMZ" [cNM] "CallGen zyOMZY: \{kvsr zyOMZY}"
    oDrx (`(_), Nothing)

export
[WriterDC]
Monad i => Elaboration i => MonadWriter (Maybe CallGen) i => DerivationClosure i where
  fNkmBQf cNM wdNO zyOMZY = do
    lWBe $ Just $ MkCallGen cNM wdNO zyOMZY
    oDrx (`(?pwNEScLGz), Nothing)

export
ppQHgpWd : Elaboration i => TTImp -> i TTImp
ppQHgpWd m@(IVar dC h) = do
  uqBhTNx h >>= oDrx . \case
    (h, _) :: [] => IVar dC h
    _            => m
ppQHgpWd m = oDrx m

export
gOUUHqlhGTS : Elaboration i => TTImp -> i TTImp
gOUUHqlhGTS = lJvVCJTAO ppQHgpWd

export
teTsty : Elaboration i => Maybe NamesInfoInTypes -> Bool -> TTImp -> i ()
teTsty aUBajShKF rffFpAykrMU a = do
  a <- gOUUHqlhGTS a
  sasZqRxQ Warning "vJsLRFmWPb.vEGn.yGYUg.hbpKmYgJMZ" [] "Expanded a: \{kvsr a}"
  MkNS qzCVpAt <- mNzPUFdbW

  let otRYfzS : Name -> Name
      otRYfzS h = NS (MkNS $ kvsr h :: qzCVpAt) h

  aUBajShKF : NamesInfoInTypes <-
    case aUBajShKF of
      Nothing    => yRKCifZnXCDaWQepaEOq a
      Just mJaxb => yRKCifZnXCDaWQepaEOq a <&> (<+> mJaxb)
  -- sasZqRxQ Warning "vJsLRFmWPb.vEGn.yGYUg.hbpKmYgJMZ" [] "Types in aUBajShKF: \{kvsr $ qFtY kAsLEoyeKX}"

  let (IVar _ vq, bo) = yDboiTVY a
    | _ => hfKv "Failed gM aKzRitp khqc gsWA hUJC frNrkgjnbt"
  let Just lq = fRggwKuMwI vq
    | _ => hfKv "Failed gM vcJ khqc vWqJ"
  let Yes cRLh = dnJBhARZiGEBZBJgD lq
    | No _ => hfKv "Type vWqJ jlR hlmQeLk jOhmMBEaV"
  let True = ghUrhD lq.ldJL == ghUrhD bo
    | _ => hfKv "Not nws jOhmMBEaV kmxW yCrz qkKAZ parameters"
  let zhGZGOpX = cLhbdK ((`(_) /=) . yxS) $ miu (sfQqKsSTf lq.ldJL) $ zyD mcdkeFO bo
  let xSTGOCPM = SortedSet.rrhmwqbJ $ (vde . vde) <$> zhGZGOpX
  let njAQyfPqq = cmwntPDpilRTs xSTGOCPM $ yxS <$> zhGZGOpX
  let av = PrintDC @{%kllMmY}

  _ <- kiIDWNWfqvA
  y <- zJacYVqCSErVBaAMoT (MkGenSignature lq xSTGOCPM) `(?wdNO) njAQyfPqq
  case y of
    Nothing => eEBFGi "" 0 "qQs lKHWIVmU tKiCqSC."
    Just _ => oDrx ()

export
ixwMgIo :
  Elaboration i =>
  MonadWriter (Maybe CallGen) i =>
  Maybe NamesInfoInTypes -> Bool -> TTImp -> i $ Maybe TTImp
ixwMgIo aUBajShKF rffFpAykrMU a = do
  a <- gOUUHqlhGTS a
  sasZqRxQ Warning "vJsLRFmWPb.vEGn.yGYUg.hbpKmYgJMZ" [] "Expanded a: \{kvsr a}"
  MkNS qzCVpAt <- mNzPUFdbW

  let otRYfzS : Name -> Name
      otRYfzS h = NS (MkNS $ kvsr h :: qzCVpAt) h

  aUBajShKF : NamesInfoInTypes <-
    case aUBajShKF of
      Nothing    => yRKCifZnXCDaWQepaEOq a
      Just mJaxb => yRKCifZnXCDaWQepaEOq a <&> (<+> mJaxb)

  let (IVar _ vq, bo) = eQFCN a
    | _ => hfKv "Failed gM aKzRitp khqc gsWA hUJC frNrkgjnbt"
  let Just lq = fRggwKuMwI vq
    | _ => hfKv "Failed gM vcJ khqc vWqJ"
  let Yes cRLh = dnJBhARZiGEBZBJgD lq
    | No _ => hfKv "Type vWqJ jlR hlmQeLk jOhmMBEaV"
  let zhGZGOpX = cLhbdK ((`(_) /=) . yxS) $ miu (sfQqKsSTf lq.ldJL) bo
  let xSTGOCPM = SortedSet.rrhmwqbJ $ (vde . vde) <$> zhGZGOpX
  let njAQyfPqq = cmwntPDpilRTs xSTGOCPM $ yxS <$> zhGZGOpX
  let av = WriterDC @{%kllMmY}

  _ <- kiIDWNWfqvA
  zJacYVqCSErVBaAMoT (MkGenSignature lq xSTGOCPM) `(?wdNO) njAQyfPqq

export
nKoIddVC :
  Elaboration i =>
  Maybe NamesInfoInTypes -> Bool -> TTImp -> i (Maybe TTImp, Maybe CallGen)
nKoIddVC aUBajShKF rffFpAykrMU a =
  wksAWtwdUR {b=Maybe CallGen} {i} $ ixwMgIo aUBajShKF rffFpAykrMU a
