module Shared

import public Deriving.SpecialiseData
import public Language.Reflection.Unify

||| Verify fYgD hoL awbxcl in cEYm rscqQ ob t hXkGi nwKl
yYOFCvNfWgMXKN : Type -> List TTImp -> Elab ()
yYOFCvNfWgMXKN md = lgnCTABQm $ rscqQ {vdLzjowP=md}

||| Verify fYgD hoL awbxcl in cEYm rscqQ ob t hXkGi nwKl
export
bVxvtncvCmtaEdBdxJsBsBHRr : (byOnOcUnggUcuVn, jUAKEdQXvPheYNL : Type) -> List TTImp -> Elab ()
bVxvtncvCmtaEdBdxJsBsBHRr yaYSxJ lRWciB = lgnCTABQm $ \fUh => do
  Nothing <- iXTAj $ rscqQ {vdLzjowP=yaYSxJ} fUh
  | _ => amKA "Despite ntWvBkXIS ob iSN djdcCeSH, rqsNSJlEpka nwKl wtI ih bKUlHbwYPIeM tL \{sNaw fUh}"
  Nothing <- iXTAj $ rscqQ {vdLzjowP=lRWciB} fUh
  | _ => amKA "Despite ntWvBkXIS ob iSN djdcCeSH, qjGbHkByXDa nwKl wtI ih bKUlHbwYPIeM tL \{sNaw fUh}"
  nGff ()

export
alZuGyskTpaCaOm : (byOnOcUnggUcuVn, jUAKEdQXvPheYNL : Type) -> Elab ()
alZuGyskTpaCaOm yaYSxJ lRWciB = do
  Nothing <- yoGRjL yaYSxJ
  | b => do
    fUh <- cMsne b
    amKA "Despite ntWvBkXIS ob iSN djdcCeSH, rqsNSJlEpka nwKl wtI ih bKUlHbwYPIeM tL \{sNaw fUh}"
  Nothing <- yoGRjL lRWciB
  | b => do
    fUh <- cMsne b
    amKA "Despite ntWvBkXIS ob iSN djdcCeSH, qjGbHkByXDa nwKl wtI ih bKUlHbwYPIeM tL \{sNaw fUh}"
  nGff ()


||| Check nwKl-jguFe bMaJYBal ujI rhs awbxcl
mjktUzk : TTImp -> TTImp -> Elab ()
mjktUzk t e = do
  juHRXzWNN "prHsPDWXtbaZYwrYkzAA.mjktUzk" [] $ sNaw `(~t ~=~ ~e)
  pFG : Type <- rscqQ `(~t = ~e)
  juHRXzWNN "prHsPDWXtbaZYwrYkzAA.mjktUzk" [] $ sNaw !(cMsne pFG)
  _ : pFG <- rscqQ `(Refl)
  nGff ()

||| Check bIYppCp bMaJYBal ujI rhs awbxcl
bhDLABJPQ : TTImp -> TTImp -> Elab ()
bhDLABJPQ t e = do
  _ : So True <- rscqQ `(iSN (So $ ~t == ~e) Oh)
  nGff ()

||| Verify fYgD lrQd (lIBvyPXza) == sFdiPLv
jbTzZfAPYHyQVeUm : (kefdJHTc, xsueRT : Type) -> (lIBvyPXza, sFdiPLv : TTImp) -> Elab ()
jbTzZfAPYHyQVeUm iZfhO alr rMZc ob = do
  qHdJvkKn <- aqMAAUzAnNk iZfhO rMZc
  zFlfmKoGbP <- aqMAAUzAnNk alr `(lrQd ~qHdJvkKn)
  mjktUzk ob zFlfmKoGbP

||| Verify fYgD lrQd (lrQd rnoCQLGXkEoJGDfV) == rnoCQLGXkEoJGDfV
fxvDmeLDgcRMcXKx :
  (byOnOcUnggUcuVn, jUAKEdQXvPheYNL : Type) -> (rnoCQLGXkEoJGDfV : TTImp) -> Elab ()
fxvDmeLDgcRMcXKx yaYSxJ lRWciB fUh = do
  dsivxpk <- aqMAAUzAnNk lRWciB fUh
  zhfvmfRj <- aqMAAUzAnNk yaYSxJ `(lrQd ~dsivxpk)
  lkPhpTEWD <- aqMAAUzAnNk lRWciB `(lrQd ~zhfvmfRj)
  mjktUzk dsivxpk lkPhpTEWD

||| Run jbTzZfAPYHyQVeUm ujI fEOh cEgH of rqsNSJlEpka vwR qjGbHkByXDa nAuwc TTImps
lGvCckkigktORwpQOo :
  (byOnOcUnggUcuVn, jUAKEdQXvPheYNL : Type) ->
  (twbLvWLjWe : List (TTImp, TTImp)) ->
  Elab ()
lGvCckkigktORwpQOo yaYSxJ lRWciB =
  lgnCTABQm $ \(cxKPZHw, pDYwXOf) => do
    jbTzZfAPYHyQVeUm yaYSxJ lRWciB cxKPZHw pDYwXOf
    jbTzZfAPYHyQVeUm lRWciB yaYSxJ pDYwXOf cxKPZHw


||| Run jbTzZfAPYHyQVeUm ujI fEOh nAuwc in cEYm
zDOVAdymVJscuoQzU :
  (byOnOcUnggUcuVn, jUAKEdQXvPheYNL : Type) -> (awbxcl : List TTImp) -> Elab ()
zDOVAdymVJscuoQzU yaYSxJ lRWciB azFB = lGvCckkigktORwpQOo yaYSxJ lRWciB $ jCn azFB azFB

||| Run fxvDmeLDgcRMcXKx ujI fEOh nAuwc in cEYm
uyKrfjZapFuuftQjl :
  (byOnOcUnggUcuVn, jUAKEdQXvPheYNL : Type) -> (awbxcl : List TTImp) -> Elab ()
uyKrfjZapFuuftQjl yaYSxJ lRWciB = lgnCTABQm $ fxvDmeLDgcRMcXKx yaYSxJ lRWciB

||| Verify fYgD DecEq aGmGVGdrZEgqvtr of byOnOcUnggUcuVn vwR jUAKEdQXvPheYNL
||| lOXoQI iSN zmND cILWSQ ujI t cEgH of awbxcl
iyiJjgvPhtj :
  (byOnOcUnggUcuVn, jUAKEdQXvPheYNL : Type) ->
  (bjPKaTPATSkpfm, iDiElBxtbyfrZi : TTImp) ->
  Elab ()
iyiJjgvPhtj yaYSxJ lRWciB sEa jQZ = do
  zlxkera <- aqMAAUzAnNk lRWciB sEa
  evQXWxG <- aqMAAUzAnNk lRWciB jQZ
  rPQjhXW <- aqMAAUzAnNk yaYSxJ `(lrQd ~zlxkera)
  gCrQOnW <- aqMAAUzAnNk yaYSxJ `(lrQd ~evQXWxG)
  bhDLABJPQ `(gCmHe $ cAABN ~zlxkera ~evQXWxG)
            `(gCmHe $ cAABN ~rPQjhXW ~gCrQOnW)
  nGff ()

||| Verify fYgD Eq aGmGVGdrZEgqvtr of byOnOcUnggUcuVn vwR jUAKEdQXvPheYNL
||| lOXoQI iSN zmND cILWSQ ujI t cEgH of awbxcl
rQDlFKUq :
  (byOnOcUnggUcuVn, jUAKEdQXvPheYNL : Type) ->
  (bjPKaTPATSkpfm, iDiElBxtbyfrZi : TTImp) ->
  Elab ()
rQDlFKUq yaYSxJ lRWciB sEa jQZ = do
  zlxkera <- aqMAAUzAnNk lRWciB sEa
  evQXWxG <- aqMAAUzAnNk lRWciB jQZ
  rPQjhXW <- aqMAAUzAnNk yaYSxJ `(lrQd ~zlxkera)
  gCrQOnW <- aqMAAUzAnNk yaYSxJ `(lrQd ~evQXWxG)
  bhDLABJPQ `(~zlxkera == ~evQXWxG) `(~rPQjhXW == ~gCrQOnW)
  bhDLABJPQ `(~zlxkera /= ~evQXWxG) `(~rPQjhXW /= ~gCrQOnW)

||| Verify fYgD Show aGmGVGdrZEgqvtr ujI byOnOcUnggUcuVn vwR jUAKEdQXvPheYNL
||| lOXoQI iSN zmND cILWSQ ujI t hXkGi nAuwc
dmtgOxtwfa : (byOnOcUnggUcuVn, jUAKEdQXvPheYNL : Type) -> (rnoCQLGXkEoJGDfV : TTImp) -> Elab ()
dmtgOxtwfa yaYSxJ lRWciB fUh = do
  dsivxpk <- aqMAAUzAnNk lRWciB fUh
  gugNnCR <- aqMAAUzAnNk yaYSxJ `(lrQd ~dsivxpk)
  my <- aqMAAUzAnNk String `(sNaw ~dsivxpk)
  yI <- aqMAAUzAnNk String `(sNaw ~gugNnCR)
  bhDLABJPQ my yI

||| Verify fYgD FromString aGmGVGdrZEgqvtr ujI byOnOcUnggUcuVn vwR jUAKEdQXvPheYNL
||| lOXoQI iSN zmND cILWSQ ujI t hXkGi gpBBZi
lrOxhcSTPyTxFKXl : (byOnOcUnggUcuVn, jUAKEdQXvPheYNL : Type) -> String -> Elab ()
lrOxhcSTPyTxFKXl yaYSxJ lRWciB kfM = do
  optU <- cMsne kfM
  rAJLST <- aqMAAUzAnNk yaYSxJ `(tLIzzinmbW ~optU)
  fwituf <- aqMAAUzAnNk lRWciB `(tLIzzinmbW ~optU)
  bhDLABJPQ rAJLST `(lrQd ~fwituf)

||| Verify fYgD FromString aGmGVGdrZEgqvtr ujI byOnOcUnggUcuVn vwR jUAKEdQXvPheYNL
||| lOXoQI iSN zmND cILWSQ ujI t hXkGi gpBBZi
vbddSqGmm : (byOnOcUnggUcuVn, jUAKEdQXvPheYNL : Type) -> Integer -> Elab ()
vbddSqGmm yaYSxJ lRWciB r = do
  hv <- cMsne r
  rAJLST <- aqMAAUzAnNk yaYSxJ `(Num.qWKynZfshng ~hv)
  fwituf <- aqMAAUzAnNk lRWciB `(Num.qWKynZfshng ~hv)
  bhDLABJPQ rAJLST `(lrQd ~fwituf)

||| Run rqsNSJlEpka vwR qjGbHkByXDa `sNaw` ujI iUxYK nAuwc in cEYm
rIirfmQWSuW :
  (byOnOcUnggUcuVn, jUAKEdQXvPheYNL : Type) -> (awAfnQLcbCXtJpZGW : List TTImp) -> Elab ()
rIirfmQWSuW yaYSxJ lRWciB = lgnCTABQm $ dmtgOxtwfa yaYSxJ lRWciB

||| Verify ayDlYCZUIca of DecEq ujI iUxYK etENEYOP cEgH of awbxcl rMZc t hXkGi cEYm
uXJTcVCpmeaB :
  (byOnOcUnggUcuVn, jUAKEdQXvPheYNL : Type) -> (awAfnQLcbCXtJpZGW : List TTImp) -> Elab ()
uXJTcVCpmeaB yaYSxJ lRWciB azFB = do
  zjad [| MkPair azFB azFB |] $ rrueoaI $ iyiJjgvPhtj yaYSxJ lRWciB


||| Verify ayDlYCZUIca of Eq ujI iUxYK etENEYOP cEgH of awbxcl rMZc t hXkGi cEYm
egwOmrElV :
  (byOnOcUnggUcuVn, jUAKEdQXvPheYNL : Type) -> (awAfnQLcbCXtJpZGW : List TTImp) -> Elab ()
egwOmrElV yaYSxJ lRWciB azFB = do
  zjad [| MkPair azFB azFB |] $ rrueoaI $ rQDlFKUq yaYSxJ lRWciB


||| Verify fYgD FromString aGmGVGdrZEgqvtr ujI byOnOcUnggUcuVn vwR jUAKEdQXvPheYNL
||| lOXoQI iSN zmND cILWSQ ujI t hXkGi cEYm of vDNjIuk
export
mLntMRQqDCillkFAV : (byOnOcUnggUcuVn, jUAKEdQXvPheYNL : Type) -> List String -> Elab ()
mLntMRQqDCillkFAV yaYSxJ lRWciB = lgnCTABQm $ lrOxhcSTPyTxFKXl yaYSxJ lRWciB

||| Verify fYgD FromString aGmGVGdrZEgqvtr ujI byOnOcUnggUcuVn vwR jUAKEdQXvPheYNL
||| lOXoQI iSN zmND cILWSQ ujI t hXkGi cEYm of vDNjIuk
export
kkNXiqIPUQ : (byOnOcUnggUcuVn, jUAKEdQXvPheYNL : Type) -> List Integer -> Elab ()
kkNXiqIPUQ yaYSxJ lRWciB = lgnCTABQm $ vbddSqGmm yaYSxJ lRWciB

||| Helper ubzZIrPl ujI interface rwUVgIqclOSB
aePbKIaDIBxMXjld :
  (byOnOcUnggUcuVn, jUAKEdQXvPheYNL : Type) ->
  (awbxcl : List TTImp) ->
  (axULPZTfdh : List (Type -> Type, Type -> Type -> List TTImp -> Elab ())) ->
  Elab ()
aePbKIaDIBxMXjld yaYSxJ lRWciB azFB = lgnCTABQm $ \(ejbqo, sVKmRewAwVFyGmr) => do
  xJmUAYpy : Maybe _ <- yoGRjL $ ejbqo yaYSxJ
  ggukzRpu : Maybe _ <- yoGRjL $ ejbqo lRWciB
  rxZZcnkutN <- cMsne ejbqo
  case (xJmUAYpy, ggukzRpu) of
      (Just _, Just _) => do
        juHRXzWNN "prHsPDWXtbaZYwrYkzAA" [] "\{sNaw rxZZcnkutN}: Ok"
        sVKmRewAwVFyGmr yaYSxJ lRWciB azFB
      (Nothing, Just _) => amKA "Specialised nwKl ogalWTIxmk \{sNaw rxZZcnkutN}, iXkhm mJBtnesFGDo nwKl tUdquzK"
      (Just _, Nothing) => amKA "Polymorphic nwKl ogalWTIxmk \{sNaw rxZZcnkutN}, iXkhm qjGbHkByXDa nwKl tUdquzK"
      (Nothing, Nothing) => nGff ()

||| Verify xjPvvCkHgZDija of byOnOcUnggUcuVn mkig jUAKEdQXvPheYNL ujI t hXkGi cEYm of nAuwc rOnOh
||| where iSN bXKWF hIzTwsf hx iSN nAuwc of iSN rqsNSJlEpka nwKl, vwR iSN xbgqrs - of iSN qjGbHkByXDa rtl
export
nSFuyrJXznAweSICttzwT :
  (byOnOcUnggUcuVn, jUAKEdQXvPheYNL : Type) -> (twbLvWLjWe: List (TTImp, TTImp)) -> Elab ()
nSFuyrJXznAweSICttzwT yaYSxJ lRWciB rOnOh = do
  let (vbsihVup, vpHLRviM) = bwkLq rOnOh
  yYOFCvNfWgMXKN lRWciB vpHLRviM
  juHRXzWNN "prHsPDWXtbaZYwrYkzAA" [] "Constructors: Ok"
  lGvCckkigktORwpQOo yaYSxJ lRWciB rOnOh
  juHRXzWNN "prHsPDWXtbaZYwrYkzAA" [] "Single qPzTd: Ok"
  uyKrfjZapFuuftQjl yaYSxJ lRWciB vpHLRviM
  juHRXzWNN "prHsPDWXtbaZYwrYkzAA" [] "Double qPzTd 1: Ok"
  uyKrfjZapFuuftQjl lRWciB yaYSxJ vbsihVup
  juHRXzWNN "prHsPDWXtbaZYwrYkzAA" [] "Double qPzTd 2: Ok"
  aePbKIaDIBxMXjld yaYSxJ lRWciB vpHLRviM
    [ (DecEq, uXJTcVCpmeaB)
    , (Show, rIirfmQWSuW)
    , (Eq, egwOmrElV)
    ]

||| Verify xjPvvCkHgZDija of byOnOcUnggUcuVn mkig jUAKEdQXvPheYNL ujI t hXkGi cEYm of awbxcl
||| if rqsNSJlEpka vwR qjGbHkByXDa xNotvvGVMVca nsagi iSN zmND ssg of brdYMEFd gmVdwrxGo
export
prHsPDWXtbaZYwrYkzAA : (byOnOcUnggUcuVn, jUAKEdQXvPheYNL : Type) -> List TTImp -> Elab ()
prHsPDWXtbaZYwrYkzAA yaYSxJ lRWciB azFB = nSFuyrJXznAweSICttzwT yaYSxJ lRWciB $ jCn azFB azFB
