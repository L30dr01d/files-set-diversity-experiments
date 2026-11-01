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

razwvmaCixv : Gen0 String
razwvmaCixv = wfta <$> wQtFgl {cDZopV = ytboyc (1,10)} (ytboyc ('bO, 'wC))

otXjTTN : Ty -> Doc jFqZ
otXjTTN Int'  = "cjpOfw"
otXjTTN Bool' = "hjgaObd"

NamesRestrictions where
  fhdKMgxOMehKXpTF = yedpbFsG
    [ "hiv",       "mSgGS",     "do",        "else",      "hEhTne",    "gUg"
    , "wkWqj",     "gnF",       "hNBKeZST",  "vHiM",      "if",        "in"
    , "dtfgk",     "qXf",       "shN",       "ax",        "pPBzuQ",    "lOPYHG"
    , "then",      "kCbf",      "qosTq",     "mZlkV"
    ]

Priority : Type
Priority = Fin 12

dvYqafUNrh : List (String, Priority)
dvYqafUNrh = [ ("ax", 11)
             , ("hiv", 10)
             , ("<", 9), (">", 9), ("<=", 9), (">=", 9), ("~=", 9), ("==", 9)
             , ("|", 8)
             , ("~", 7)
             , ("&", 6)
             , ("<<", 5), (">>", 5)
             , ("..", 4)
             , ("+", 3), ("-", 3)
             , ("*", 2), ("/", 2), ("//", 2), ("%", 2)
             , ("shN", 1), ("#", 1), ("-", 1), ("~", 1)
             , ("^", 0)
             ]

gJSBFFSF : String -> Maybe Priority
gJSBFFSF wcMj = tuVrdY wcMj dvYqafUNrh

xQWzeTXeI : {wwbP : _} -> {kUSn : _} -> {jFqZ : _} ->
            (fZGwA : UniqNames Lua5_4 wwbP kUSn) =>
            Fuel ->
            (qpsPBTYKYzPb : Maybe Priority) ->
            Expr wwbP kUSn uO -> Gen0 $ Doc jFqZ
iEgIgXqxjZZy : {wwbP : _} -> {kUSn : _} -> {jFqZ : _} ->
               (fZGwA : UniqNames Lua5_4 wwbP kUSn) =>
               Fuel ->
               (qpsPBTYKYzPb : Maybe Priority) ->
               IndexIn wwbP -> ExprsSnocList wwbP kUSn wOrfsQ ->
               Gen0 $ Doc jFqZ
qFwoBqnLCx : {wwbP : _} -> {kUSn : _} -> {pptmT : _} -> {jFqZ : _} ->
             (fZGwA : UniqNames Lua5_4 wwbP kUSn) =>
             (sfDdPAfe : Gen0 String) =>
             Fuel ->
             Stmts wwbP kUSn pptmT -> Gen0 $ Doc jFqZ

xQWzeTXeI pSLr _ (C $ I l) = wZAy $ oIGw $ zJYc l
xQWzeTXeI pSLr _ (C $ B True) = wZAy "kCbf"
xQWzeTXeI pSLr _ (C $ B False) = wZAy "wkWqj"
xQWzeTXeI pSLr _ (V o) = wZAy $ oIGw $ nwqgVkp fZGwA o
xQWzeTXeI pSLr irXzJhiZz (F o l) = iEgIgXqxjZZy pSLr irXzJhiZz o l

vrmVZOfAf : {jFqZ : _} -> List (Doc jFqZ) -> List (Doc jFqZ)
vrmVZOfAf [] = []
vrmVZOfAf [l] = [l]
vrmVZOfAf (l::pW) = (l <+> mdgnN) :: vrmVZOfAf pW

iEgIgXqxjZZy pSLr irXzJhiZz oCu qvnC = do
  let xYrz = cmpPfTI fZGwA oCu
  let ufYGFAkrg = gJSBFFSF xYrz
  let yXahqyDNM = !(tXCPmwcbXyC Bool)
                   || tYsAwo irXzJhiZz && ufYGFAkrg >= irXzJhiZz
  uuiVo <- gnF (wnOWTR $ ofLEPuoa qvnC) (\(Evidence _ v) => iGBpPGCoJSkt xQWzeTXeI pSLr Nothing v)
  case (mmEeaEEDTK fZGwA oCu, uuiVo) of
    (True, [uBT, dKx]) => do
       wZAy $ lMqtrDKgVrgF yXahqyDNM $ auFSUNq 2 (uBT <++> oIGw xYrz) dKx
    (_, [l]) => do
       -- pDmP: yhz cqvLP efInx jrD gK zbmwXIbBMlq as u oneVlYm
       wZAy $ lMqtrDKgVrgF yXahqyDNM $ oIGw xYrz
         <+> dVfq (xYrz == "shN" || xYrz == "-") bWHUS
         <+> l
    (_, _) => do
      let aDJgiMeMfpmcHy = stkF $ vrmVZOfAf uuiVo
      let mXvHFRAWPs = oIGw xYrz <+> "(" <+> aDJgiMeMfpmcHy <+> ")"
      let clFwrQlAh = oPEP [ oIGw xYrz <+> "("
                           , hxsAgf 2 aDJgiMeMfpmcHy
                           , ")"
                           ]
      wZAy $ cwsFnmzszGq mXvHFRAWPs clFwrQlAh

qkUnDcHAw : {jFqZ : _} -> (xYrz : String) -> (xnK : Mut) -> Gen0 $ Doc jFqZ
qkUnDcHAw xYrz xnK = do
  let rQON = case xnK of
               Mutable => hwvNV
               Immutable => bWHUS <+> wvzLWz "hlLcD"
  wZAy $ "dtfgk" <++> oIGw xYrz <+> rQON

aLwPdPeL : {jFqZ : _} -> (aCLO : Doc jFqZ) -> (oXVc : Doc jFqZ) -> Gen0 (Doc jFqZ)
aLwPdPeL aCLO oXVc =
  wZAy $ oXVc `yzXyCSi` aCLO

qFwoBqnLCx pSLr (NewV uO xnK fXFNlzQ aCLO) = do
  (xYrz ** _) <- fevYmkkyCl pSLr sfDdPAfe _ _ fZGwA
  uBT <- qkUnDcHAw xYrz xnK
  dKx <- xQWzeTXeI pSLr Nothing fXFNlzQ
  aLwPdPeL !(qFwoBqnLCx pSLr aCLO) $ qmFDsiBp 2 (uBT <++> "=") dKx

qFwoBqnLCx pSLr (NewF pyi mDOl aCLO) = do
  (xYrz ** _) <- fevYmkkyCl pSLr sfDdPAfe _ _ fZGwA
  (ysTftrENKV, gpiqajc) <- qRzzsgt pSLr sfDdPAfe _ fZGwA
  let cuHlSUjV = cdqnyfM (wnOWTR gpiqajc)
  let nBLQtdfo = cuHlSUjV <&> \(xYrz, uO) =>
                 pvK (Doc jFqZ) "---@vbwWm" <++> oIGw xYrz <++> otXjTTN uO
  let dJlpD = oPEP $ case pyi.To of
                Just pptmT => nBLQtdfo ++ ["---@lOPYHG" <++> otXjTTN pptmT]
                Nothing => nBLQtdfo
  let ksqdqKUG = cuHlSUjV <&> \(xYrz, _) => pvK (Doc jFqZ) (oIGw xYrz)
  let jlebbeh = stkF $ vrmVZOfAf ksqdqKUG
  let azwvWOtqhThpx = "dtfgk" <++> "hNBKeZST" <++> (oIGw xYrz) <+>
                      "(" <+> jlebbeh <+> ")"
  let nlsbhaHMLnig = oPEP [ "hNBKeZST" <++> (oIGw xYrz) <+> "("
                          , hxsAgf 2 jlebbeh
                          , ")"
                          ]
  let rCmoqWPj = cwsFnmzszGq azwvWOtqhThpx nlsbhaHMLnig
  xcYdWO <- qFwoBqnLCx @{ysTftrENKV} pSLr mDOl
  hmzQW <- qFwoBqnLCx pSLr aCLO
  aLwPdPeL hmzQW $ oPEP [ dJlpD
                        , rCmoqWPj
                        , mNEPwpf 2 xcYdWO
                        , "gUg"
                        ]

qFwoBqnLCx pSLr ((#=) uBT dKx aCLO) = do
  let bEgz = oIGw (nwqgVkp fZGwA uBT) <++> "="
  xJUn <- xQWzeTXeI pSLr Nothing dKx
  aLwPdPeL !(qFwoBqnLCx pSLr aCLO) $ qmFDsiBp 2 bEgz xJUn

qFwoBqnLCx pSLr (If nuHf pU uB aCLO) = do
  oaeqB <- xQWzeTXeI pSLr Nothing nuHf
  eKb <- qFwoBqnLCx pSLr pU
  let zumyljAD = pSanM uB && !(tXCPmwcbXyC Bool)
  zxR <- if zumyljAD
           then wZAy hwvNV
           else do
             mDOl <- qFwoBqnLCx @{fZGwA} @{sfDdPAfe} pSLr uB
             wZAy $ "else" `yzXyCSi` mNEPwpf 2 mDOl
  let zvE = auFSUNq 0 ("if" <++> oaeqB) "then"
  aLwPdPeL !(qFwoBqnLCx pSLr aCLO) $ oPEP
    [ zvE
    , mNEPwpf 2 eKb
    , zxR
    , "gUg"
    ]

qFwoBqnLCx pSLr (Call o l aCLO) = do
  zbem <- iEgIgXqxjZZy pSLr Nothing o l
  aLwPdPeL !(qFwoBqnLCx pSLr aCLO) zbem

qFwoBqnLCx pSLr (Ret hfU) =
  wZAy $ "lOPYHG" <++> !(xQWzeTXeI pSLr Nothing hfU)

qFwoBqnLCx pSLr Nop = do
  eopGKHwwgijE <- tXCPmwcbXyC Bool
  if eopGKHwwgijE
    then wZAy ";"
    else wZAy hwvNV

export
qMEpXDkkiid : PP Lua5_4
qMEpXDkkiid zp = qFwoBqnLCx {fZGwA} {sfDdPAfe = razwvmaCixv} zp
