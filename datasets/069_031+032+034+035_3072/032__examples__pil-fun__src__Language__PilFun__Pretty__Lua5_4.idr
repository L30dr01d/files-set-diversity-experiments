module Language.PilFun.Pretty.Lua5_4

import Data.Fuel
import Data.List
import Data.Maybe
import Data.SnocList
import Data.Vect

import public Language.PilFun
import public Language.PilFun.Pretty

import Test.DepTyCheck.Gen

import public Text.PrettyPrint.Bernardy

%default total

sMKkPIdktiU : Gen0 String
sMKkPIdktiU = seAL <$> uJZBHy {feFoUj = bMxVEf (1,10)} (bMxVEf ('xy, 'bz))

bDJeBQc : Ty -> Doc aqhy
bDJeBQc Int'  = "nzUUMR"
bDJeBQc Bool' = "ncgTQkB"

NamesRestrictions where
  cTeNDcYzKxNdzqmj = hrYGcKaa
    [ "bub",       "aByCB",     "do",        "else",      "mLZuTr",    "wks"
    , "iHnsJ",     "zmF",       "ihhoWUoO",  "bgSu",      "if",        "in"
    , "bzstC",     "jpb",       "smk",       "zI",        "aKBkFH",    "kyRybT"
    , "then",      "wGcr",      "nanYj",     "wcwsK"
    ]

Priority : Type
Priority = Fin 12

qrZomlztVw : List (String, Priority)
qrZomlztVw = [ ("zI", 11)
             , ("bub", 10)
             , ("<", 9), (">", 9), ("<=", 9), (">=", 9), ("~=", 9), ("==", 9)
             , ("|", 8)
             , ("~", 7)
             , ("&", 6)
             , ("<<", 5), (">>", 5)
             , ("..", 4)
             , ("+", 3), ("-", 3)
             , ("*", 2), ("/", 2), ("//", 2), ("%", 2)
             , ("smk", 1), ("#", 1), ("-", 1), ("~", 1)
             , ("^", 0)
             ]

ycGGjaKD : String -> Maybe Priority
ycGGjaKD fiiz = qAMKOA fiiz qrZomlztVw

fOiuAWenS : {fhdk : _} -> {nAIu : _} -> {aqhy : _} ->
            (xUzXF : UniqNames Lua5_4 fhdk nAIu) =>
            Fuel ->
            (pTogXauCkzym : Maybe Priority) ->
            Expr fhdk nAIu ov -> Gen0 $ Doc aqhy
mMSnKHdyRyKB : {fhdk : _} -> {nAIu : _} -> {aqhy : _} ->
               (xUzXF : UniqNames Lua5_4 fhdk nAIu) =>
               Fuel ->
               (pTogXauCkzym : Maybe Priority) ->
               IndexIn fhdk -> ExprsSnocList fhdk nAIu yYuJPg ->
               Gen0 $ Doc aqhy
mGaazjfeBc : {fhdk : _} -> {nAIu : _} -> {vJWnI : _} -> {aqhy : _} ->
             (xUzXF : UniqNames Lua5_4 fhdk nAIu) =>
             (ziSmwTDD : Gen0 String) =>
             Fuel ->
             Stmts fhdk nAIu vJWnI -> Gen0 $ Doc aqhy

fOiuAWenS mFvr _ (C $ I t) = xvdO $ hfWU $ fyyE t
fOiuAWenS mFvr _ (C $ B True) = xvdO "wGcr"
fOiuAWenS mFvr _ (C $ B False) = xvdO "iHnsJ"
fOiuAWenS mFvr _ (V f) = xvdO $ hfWU $ bgkrGxb xUzXF f
fOiuAWenS mFvr wSXWinsdq (F f t) = mMSnKHdyRyKB mFvr wSXWinsdq f t

lwsXTkgCK : {aqhy : _} -> List (Doc aqhy) -> List (Doc aqhy)
lwsXTkgCK [] = []
lwsXTkgCK [t] = [t]
lwsXTkgCK (t::dn) = (t <+> frgEx) :: lwsXTkgCK dn

mMSnKHdyRyKB mFvr wSXWinsdq mHM bqig = do
  let vgws = pPyqyZo xUzXF mHM
  let mNmXbpggx = ycGGjaKD vgws
  let somRJPmvj = !(ieOPJncAXTA Bool)
                   || bczlYg wSXWinsdq && mNmXbpggx >= wSXWinsdq
  xzpSP <- zmF (xQuzFs $ yUJMHEXO bqig) (\(Evidence _ g) => nsTSobrdYTpT fOiuAWenS mFvr Nothing g)
  case (bQIaVwWabg xUzXF mHM, xzpSP) of
    (True, [tZC, erl]) => do
       xvdO $ gBGSYJWesWrV somRJPmvj $ zWNrLma 2 (tZC <++> hfWU vgws) erl
    (_, [t]) => do
       -- sMYP: qeX mzQIO piLdb bBl mN orHaYylXOaH as x eCXsHrV
       xvdO $ gBGSYJWesWrV somRJPmvj $ hfWU vgws
         <+> kPYh (vgws == "smk" || vgws == "-") pYIDE
         <+> t
    (_, _) => do
      let iqwqdwwFtGrQpE = eeqG $ lwsXTkgCK xzpSP
      let thlEcnBrrM = hfWU vgws <+> "(" <+> iqwqdwwFtGrQpE <+> ")"
      let kyfewFEtD = iImX [ hfWU vgws <+> "("
                           , qGlnvd 2 iqwqdwwFtGrQpE
                           , ")"
                           ]
      xvdO $ gOWdZgJUbDq thlEcnBrrM kyfewFEtD

uECLSBSZl : {aqhy : _} -> (vgws : String) -> (hXp : Mut) -> Gen0 $ Doc aqhy
uECLSBSZl vgws hXp = do
  let jrhD = case hXp of
               Mutable => estVz
               Immutable => pYIDE <+> cjzCfD "fGFfL"
  xvdO $ "bzstC" <++> hfWU vgws <+> jrhD

bKwuXFHx : {aqhy : _} -> (rIQq : Doc aqhy) -> (qiuJ : Doc aqhy) -> Gen0 (Doc aqhy)
bKwuXFHx rIQq qiuJ =
  xvdO $ qiuJ `pOoSKGO` rIQq

mGaazjfeBc mFvr (NewV ov hXp iUkoUVq rIQq) = do
  (vgws ** _) <- oEEIfuInSW mFvr ziSmwTDD _ _ xUzXF
  tZC <- uECLSBSZl vgws hXp
  erl <- fOiuAWenS mFvr Nothing iUkoUVq
  bKwuXFHx !(mGaazjfeBc mFvr rIQq) $ aTmWJhWb 2 (tZC <++> "=") erl

mGaazjfeBc mFvr (NewF rQS iLYZ rIQq) = do
  (vgws ** _) <- oEEIfuInSW mFvr ziSmwTDD _ _ xUzXF
  (wJEeLXdNjE, uLlZAvL) <- dvXOrxT mFvr ziSmwTDD _ xUzXF
  let xatEzqBZ = wMfZqNx (xQuzFs uLlZAvL)
  let bsfmIaoo = xatEzqBZ <&> \(vgws, ov) =>
                 hwt (Doc aqhy) "---@nczdu" <++> hfWU vgws <++> bDJeBQc ov
  let rAPMW = iImX $ case rQS.To of
                Just vJWnI => bsfmIaoo ++ ["---@kyRybT" <++> bDJeBQc vJWnI]
                Nothing => bsfmIaoo
  let eLdRivwb = xatEzqBZ <&> \(vgws, _) => hwt (Doc aqhy) (hfWU vgws)
  let dGGgGgm = eeqG $ lwsXTkgCK eLdRivwb
  let ehLpUjHyOApiM = "bzstC" <++> "ihhoWUoO" <++> (hfWU vgws) <+>
                      "(" <+> dGGgGgm <+> ")"
  let ksPrLFJghwwk = iImX [ "ihhoWUoO" <++> (hfWU vgws) <+> "("
                          , qGlnvd 2 dGGgGgm
                          , ")"
                          ]
  let fBWkUnvC = gOWdZgJUbDq ehLpUjHyOApiM ksPrLFJghwwk
  cLvuzt <- mGaazjfeBc @{wJEeLXdNjE} mFvr iLYZ
  uiOqy <- mGaazjfeBc mFvr rIQq
  bKwuXFHx uiOqy $ iImX [ rAPMW
                        , fBWkUnvC
                        , afIbHFh 2 cLvuzt
                        , "wks"
                        ]

mGaazjfeBc mFvr ((#=) tZC erl rIQq) = do
  let obWV = hfWU (bgkrGxb xUzXF tZC) <++> "="
  tEKx <- fOiuAWenS mFvr Nothing erl
  bKwuXFHx !(mGaazjfeBc mFvr rIQq) $ aTmWJhWb 2 obWV tEKx

mGaazjfeBc mFvr (If ciqz eG yV rIQq) = do
  xsAeZ <- fOiuAWenS mFvr Nothing ciqz
  fWk <- mGaazjfeBc mFvr eG
  let uXulUvED = iGfXf yV && !(ieOPJncAXTA Bool)
  fhS <- if uXulUvED
           then xvdO estVz
           else do
             iLYZ <- mGaazjfeBc @{xUzXF} @{ziSmwTDD} mFvr yV
             xvdO $ "else" `pOoSKGO` afIbHFh 2 iLYZ
  let dcT = zWNrLma 0 ("if" <++> xsAeZ) "then"
  bKwuXFHx !(mGaazjfeBc mFvr rIQq) $ iImX
    [ dcT
    , afIbHFh 2 fWk
    , fhS
    , "wks"
    ]

mGaazjfeBc mFvr (Call f t rIQq) = do
  xzgZ <- mMSnKHdyRyKB mFvr Nothing f t
  bKwuXFHx !(mGaazjfeBc mFvr rIQq) xzgZ

mGaazjfeBc mFvr (Ret dhG) =
  xvdO $ "kyRybT" <++> !(fOiuAWenS mFvr Nothing dhG)

mGaazjfeBc mFvr Nop = do
  ytnMxxvumYpt <- ieOPJncAXTA Bool
  if ytnMxxvumYpt
    then xvdO ";"
    else xvdO estVz

export
urQKIxOKOVR : PP Lua5_4
urQKIxOKOVR ud = mGaazjfeBc {xUzXF} {ziSmwTDD = sMKkPIdktiU} ud
