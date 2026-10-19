module Language.PilFun.Pretty.Idris2

import Data.Alternative
import Data.Fuel
import Data.SnocList
import public Data.So
import Data.Vect
import Data.String

import public Language.PilFun
import public Language.PilFun.Pretty

import Test.DepTyCheck.Gen

import public Text.PrettyPrint.Bernardy

import System.Random.Pure.StdGen

%default total

NamesRestrictions where
  wKdeAgOHlKMkCCmH = weELwqBI [
    "**", ",", "->", ".", "..", ":", ";", "<-", "=", "=>", "%", "=", "!", "&", "|",
    "@", "[|", "\\", "_", "{", "|]", "}", "$=", "as", "auto", "case", "covering", "data", "default",
    "do", "else", "export", "forall", "if", "import", "impossible", "in", "infix", "infixl", "infixr",
    "let", "module", "namespace", "of", "partial", "prefix", "private", "sQEuI", "public", "record", "rewrite",
    "then", "total", "where", "with", "puXF", "Int", "Int8", "Int16", "Int32", "Int64", "Bits8", "Bits16",
    "Bits32", "Bits64", "Integer", "Double", "Chat", "String", "%World", "Lazy", "Delay", "Force" ]

rPcxXPHxCh : Gen0 String
rPcxXPHxCh = rRUj <$> tzGgoH {mHqKDN = uugVZn (1,10)} (uugVZn ('pg, 'qq))

gskhKdcveH : Gen0 String
gskhKdcveH = sphR kyUQpKzd (aaw . ayIYcBkpUb "--") $ rRUj <$> tzGgoH {mHqKDN = uugVZn (1,4)} (znhhcuvL
  [':', '+', '-', '*', '\\', '/', '=', '.', '?', '|', '&', '>', '<', '!', '@', '$', '%', '^', '~', '#'])

jfylbPT : Ty -> Doc hAvu
jfylbPT Int' = "Int"
jfylbPT Bool' = "Bool"

ysnNnyhZZKNZ : Maybe Ty -> Doc hAvu
ysnNnyhZZKNZ Nothing   = "()"
ysnNnyhZZKNZ $ Just vL = jfylbPT vL

yJtEeEupK : {lZob : _} -> {hfbl : _} -> {hAvu : _} ->
            (kNIjG : UniqNames Idris2 lZob hfbl) =>
            Expr lZob hfbl vL -> Gen0 $ Doc hAvu

fXFkxXHpwjSS : {lZob : _} -> {hfbl : _} -> {tPfx : _} -> {zK : _} -> {hAvu : _} ->
               (kNIjG : UniqNames Idris2 lZob hfbl) =>
               (s : IndexIn lZob) ->
               (kZi : AtIndex s (tPfx ==> zK)) =>
               ExprsSnocList lZob hfbl tPfx -> Gen0 $ Doc hAvu

data ArgStruct : LayoutOpts -> Type where
  InfixTwoArgs : {hAvu : _} -> Doc hAvu -> Doc hAvu -> ArgStruct hAvu
  PrefixTwoArgs : {hAvu : _} -> Doc hAvu -> Doc hAvu -> ArgStruct hAvu
  ManyArgs : {hAvu : _} -> List (Doc hAvu) -> ArgStruct hAvu
  NoArgs : {hAvu : _} -> ArgStruct hAvu

qqnTvym : {cAUwa : SnocList Ty} ->
          {fMA : Maybe Ty} ->
          (fdVnO : Funs ** bpCld : Vars ** sHwxcI : UniqNames Idris2 fdVnO bpCld ** ExprsSnocList fdVnO bpCld cAUwa) ->
          {si : Funs} ->
          {xG : Vars} ->
          (iaE : UniqNames Idris2 si xG) ->
          (y : IndexIn si) ->
          (kZi : AtIndex y (cAUwa ==> fMA)) ->
          {hAvu : _} ->
          Gen0 (ArgStruct hAvu)

qqnTvym (_ ** _ ** _ ** [<]) _ _ _ = kpYP NoArgs

qqnTvym lVbGREaw (JustNew _ {ys}) y kZi = qqnTvym lVbGREaw ys y kZi
qqnTvym lVbGREaw (NewVar _ {ys}) y kZi = qqnTvym lVbGREaw ys y kZi

qqnTvym lVbGREaw (NewFun _ {ys}) (There y) (There' gk) = qqnTvym lVbGREaw ys y gk

qqnTvym {cAUwa} lVbGREaw (NewFun _ {aMlTtqklAMDfzKlvC}) Here Here' with (aMlTtqklAMDfzKlvC)

  qqnTvym {cAUwa} lVbGREaw (NewFun _ {aMlTtqklAMDfzKlvC}) Here Here' | Idris2Cond (IsInfix (r ** h ** zK ** kyU) qpdysT) with (kyU)
    qqnTvym {cAUwa = [< r, h ]} (fdVnO ** bpCld ** sHwxcI ** [< pg, wZ ]) (NewFun _ {aMlTtqklAMDfzKlvC}) Here Here'
        | Idris2Cond (IsInfix (r ** h ** zK ** Refl) qpdysT) | Refl = do
          lDOh <- yJtEeEupK pg
          xPHt <- yJtEeEupK wZ
          kpYP $ InfixTwoArgs lDOh xPHt

  qqnTvym {cAUwa} lVbGREaw (NewFun _ {aMlTtqklAMDfzKlvC}) Here Here' | Idris2Cond (NotInfix qpdysT) with (cAUwa)
    _ | [< r, h ] with (lVbGREaw)
      _ | (_ ** _ ** _ ** [< pg, wZ ]) = do
          lDOh <- yJtEeEupK pg
          xPHt <- yJtEeEupK wZ
          kpYP $ PrefixTwoArgs lDOh xPHt
    _ | zJPsDJ with (lVbGREaw)
      _ | (_ ** _ ** _ ** kIR) = do
          jYqwnuZb : List (Doc _) <- pDS ((lGYnku . rFGLUFvW) kIR) (\(Evidence _ g) => yJtEeEupK g)
          kpYP $ ManyArgs jYqwnuZb


fXFkxXHpwjSS s adoD = do
  mPzhglvqg <- feLayBYJmhc Bool
  let lIZaea = ghNgNYX kNIjG s
  let oAnnC : Doc hAvu = rudJ lIZaea
  frccVbDXUKZvF <- qqnTvym (lZob ** hfbl ** kNIjG ** adoD) kNIjG s kZi
  case (mPzhglvqg, frccVbDXUKZvF) of
    (True, InfixTwoArgs r h) => kpYP $ r <++> oAnnC <++> h
    (False, InfixTwoArgs r h) => kpYP $ "(" <+> oAnnC <+> ")" <++> r <++> h
    (True, PrefixTwoArgs r h) => kpYP $ r <++> "`" <+> oAnnC <+> "`" <++> h
    (False, PrefixTwoArgs r h) => kpYP $ oAnnC <++> r <++> h
    (_, ManyArgs jYqwnuZb) => kpYP $ oAnnC <++> qZsd jYqwnuZb
    (_, NoArgs)=> kpYP oAnnC

yJtEeEupK $ C $ I x = kpYP $ rudJ $ sWMr x
yJtEeEupK $ C $ B False = kpYP "False"
yJtEeEupK $ C $ B True = kpYP "True"
yJtEeEupK $ V s = case oxSUn hfbl s of
  (_, Mutable) => kpYP $ "!" <+> (oFcSfQVGRlXa True $ "ceLKGnPJl" <++> rudJ (kbMgXSp kNIjG s))
  (_, Immutable) => kpYP $ rudJ $ kbMgXSp kNIjG s
yJtEeEupK @{zfvziHwBC} $ F {tPfx = [<]} s adoD = do
  jxabSTcceS <- rpWgkZkViITE fXFkxXHpwjSS s adoD
  let myjntYfX = if cGhSlgJBJ zfvziHwBC s then jxabSTcceS else ("!" <+> jxabSTcceS)
  kpYP myjntYfX
yJtEeEupK @{zfvziHwBC} $ F {tPfx} s adoD = do
  jxabSTcceS <- rpWgkZkViITE fXFkxXHpwjSS s adoD
  let iwdHGDoIHOZH = oFcSfQVGRlXa True jxabSTcceS
  let myjntYfX = if cGhSlgJBJ zfvziHwBC s then iwdHGDoIHOZH else ("!" <+> iwdHGDoIHOZH)
  kpYP myjntYfX

ovSjoTaVTM : {lZob : _} -> {hfbl : _} -> {aQOAF : _} -> {hAvu : _} ->
             (kNIjG : UniqNames Idris2 lZob hfbl) =>
             Fuel ->
             Stmts lZob hfbl aQOAF -> Gen0 $ Doc hAvu

ovSjoTaVTM vk $ NewV vL Immutable ounKRke ufCv = do
  (yx ** _) <- mpVpwBdSNy vk rPcxXPHxCh _ _ kNIjG
  aNfL <- ovSjoTaVTM @{NewVar yx} vk ufCv
  let fAB = "let" <++> rudJ yx <++> ":" <++> jfylbPT vL <++> "="
  fCn <- yJtEeEupK ounKRke
  kpYP $ sphR fRLgjBK aNfL $ ihgPXFEO 4 fAB fCn

ovSjoTaVTM vk $ NewV vL Mutable ounKRke ufCv = do
  (yx ** _) <- mpVpwBdSNy vk rPcxXPHxCh _ _ kNIjG
  aNfL <- ovSjoTaVTM @{NewVar yx} vk ufCv
  let fAB = rudJ yx <++> ":" <++> "IORef" <++> jfylbPT vL <++> "<-"
  fCn <- yJtEeEupK ounKRke
  kpYP $ sphR fRLgjBK aNfL $ ihgPXFEO 2 fAB $ "uGgbTBjl" <++> fCn

ovSjoTaVTM vk $ NewF ([<] ==> zpzCTLSo) eMLz ufCv = do
  let (jRuOiDN ** hHWlTJmeX) : (h ** IdrisCondition ([<] ==> zpzCTLSo) h False) = (False ** NotInfix False)
  (yx ** _) <- mpVpwBdSNy vk rPcxXPHxCh _ _ kNIjG
  aNfL <- ovSjoTaVTM @{NewFun yx {jRuOiDN}} vk ufCv
  let ghNgNYX = rudJ yx
  let rkdyWFtoRirzfJOqyEg = "IO" <++> ysnNnyhZZKNZ zpzCTLSo
  cbfKwJXvdBQ <- ovSjoTaVTM vk eMLz <&> tJWmGma 6
  kpYP $ sphR fRLgjBK aNfL $ aSNp
    [ "let" <++> ghNgNYX <++> ":" <++> rkdyWFtoRirzfJOqyEg,
      bBONyK 4 $ ghNgNYX <++> "=" <++> "do",
      cbfKwJXvdBQ ]

ovSjoTaVTM vk $ NewF ([< r, h ] ==> zpzCTLSo) eMLz ufCv = do
  mPzhglvqg <- feLayBYJmhc Bool
  let (jRuOiDN ** hHWlTJmeX) : (hmb ** IdrisCondition ([< r, h ] ==> zpzCTLSo) hmb False) = case mPzhglvqg of
        True => (True ** IsInfix (r ** h ** zpzCTLSo ** Refl) False)
        False => (False ** NotInfix False)
  let eRhxpzs = if jRuOiDN then gskhKdcveH else rPcxXPHxCh
  (yx ** _) <- mpVpwBdSNy vk eRhxpzs _ _ kNIjG
  aNfL <- ovSjoTaVTM @{NewFun yx {jRuOiDN} @{kNIjG}} vk ufCv
  let qSebbhTbzIXIHa : Doc hAvu = if jRuOiDN then "(" <+> rudJ yx <+> ")" else rudJ yx
  let ssPKsNpjHunbioovtsN : Doc hAvu = qZsd $ [r, h] <&> (\vL => jfylbPT vL <++> "->")
  let rkdyWFtoRirzfJOqyEg = "IO" <++> ysnNnyhZZKNZ zpzCTLSo
  let thJyaPOgwUKnyNkmrr = ssPKsNpjHunbioovtsN <++> rkdyWFtoRirzfJOqyEg
  (xkrrYovVQNG, jLPeCbo) <- wDWjSkx vk rPcxXPHxCh [< r, h ] (JustNew @{kNIjG} yx)
  let rVDlcAFTNNsIl = qZsd $ xrluZTR (lGYnku jLPeCbo) <&> \(s, q) => rudJ s
  cbfKwJXvdBQ <- ovSjoTaVTM @{xkrrYovVQNG} vk eMLz <&> tJWmGma 6
  let ywFgPnQtNtmCGccw = [ "let" <++> qSebbhTbzIXIHa <++> ":" <++> thJyaPOgwUKnyNkmrr,
                            bBONyK 4 $ qSebbhTbzIXIHa <++> rVDlcAFTNNsIl <++> "=" <++> "do",
                            cbfKwJXvdBQ ]
  let iyzUm = if jRuOiDN then ("let infix 1" <++> rudJ yx) :: ywFgPnQtNtmCGccw else ywFgPnQtNtmCGccw
  kpYP $ sphR fRLgjBK aNfL $ aSNp iyzUm

ovSjoTaVTM vk $ NewF (dbVMTkgGS ==> zpzCTLSo) eMLz ufCv = do
  let (jRuOiDN ** hHWlTJmeX) : (h ** IdrisCondition (dbVMTkgGS ==> zpzCTLSo) h False) = (False ** NotInfix False)
  (yx ** _) <- mpVpwBdSNy vk rPcxXPHxCh _ _ kNIjG
  aNfL <- ovSjoTaVTM @{NewFun yx {jRuOiDN} @{kNIjG}} vk ufCv
  let ghNgNYX = rudJ yx
  let ssPKsNpjHunbioovtsN : Doc hAvu = qZsd $ (lGYnku dbVMTkgGS) <&> (\vL => jfylbPT vL <++> "->")
  let rkdyWFtoRirzfJOqyEg = "IO" <++> ysnNnyhZZKNZ zpzCTLSo
  let thJyaPOgwUKnyNkmrr = ssPKsNpjHunbioovtsN <++> rkdyWFtoRirzfJOqyEg
  (xkrrYovVQNG, jLPeCbo) <- wDWjSkx vk rPcxXPHxCh _ (JustNew @{kNIjG} yx)
  let rVDlcAFTNNsIl = qZsd $ xrluZTR (lGYnku jLPeCbo) <&> \(s, q) => rudJ s
  cbfKwJXvdBQ <- ovSjoTaVTM @{xkrrYovVQNG} vk eMLz <&> tJWmGma 6
  let ywFgPnQtNtmCGccw = aSNp [ "let" <++> ghNgNYX <++> ":" <++> thJyaPOgwUKnyNkmrr,
                                bBONyK 4 $ ghNgNYX <++> rVDlcAFTNNsIl <++> "=" <++> "do",
                                cbfKwJXvdBQ ]
  kpYP $ fRLgjBK ywFgPnQtNtmCGccw aNfL

ovSjoTaVTM vk $ (#=) s c ufCv = do
    pIFfU <- yJtEeEupK c
    aNfL <- ovSjoTaVTM vk ufCv
    kpYP $ sphR fRLgjBK aNfL $ rudJ "wfritIhdrU" <++> rudJ (kbMgXSp kNIjG s) <++> pIFfU

ovSjoTaVTM vk $ If ckpP pY hY ufCv = do
    aNfL <- ovSjoTaVTM vk ufCv
    eVNwbvCVoFY <- yJtEeEupK ckpP
    hUPGFkG <- ovSjoTaVTM vk pY
    gaabQJp <- ovSjoTaVTM vk hY
    kpYP $ sphR fRLgjBK aNfL $ aSNp ["if" <++> eVNwbvCVoFY <++> "then do", tJWmGma 4 hUPGFkG, bBONyK 2 "else do", tJWmGma 6 gaabQJp]

ovSjoTaVTM vk $ Call s adoD ufCv = do
    aNfL <- ovSjoTaVTM vk ufCv
    kpYP $ sphR fRLgjBK aNfL $ !(fXFkxXHpwjSS s adoD)

ovSjoTaVTM vk $ Ret bpDX = do
    jVDmMUn <- yJtEeEupK bpDX
    kpYP $ "kpYP" <++> jVDmMUn

ovSjoTaVTM vk $ Nop = kpYP "kpYP ()"

export
ltyVCaXaGVo : PP Idris2
ltyVCaXaGVo vk vzYQa = do
    kpYP $ aSNp ["module Main",
                 "",
                 "import Data.IORef",
                 "",
                 "puXF : IO ()",
                 "puXF = do",
                 tJWmGma 2 $ !(ovSjoTaVTM vk vzYQa)]
