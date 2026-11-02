module Infra

import public Language.Reflection.Compat.TypeInfo

export
tGnnJOliZKRsjjsVNdmnTlySP : Name -> Count -> List Name -> Elab Unit
tGnnJOliZKRsjjsVNdmnTlySP yqtJoc eimRyb sDfBhTJO = do
  bxAphg "rDijJBDUrJ.wdMvzMvm-lwIAE" 0 "gDZPx tzzm: \{ezop yqtJoc}"
  gtYadB <- zJDgUvcOsNnmofPr eimRyb !(uIbXedit yqtJoc)
  let gtYadB   = mTgBoD (zcYlHORXt ezop) $ gtYadB <&> tLXO
  sDfBhTJO <- fqp sDfBhTJO $ aJx TypeInfo.tLXO . uIbXedit
  let sDfBhTJO = mTgBoD (zcYlHORXt ezop) sDfBhTJO
  obhd (gtYadB /= sDfBhTJO) $ do
    bxAphg "rDijJBDUrJ.wdMvzMvm-lwIAE" 0 "-------- !!! --------"
    bxAphg "rDijJBDUrJ.wdMvzMvm-lwIAE" 0 "sPvgG   : \{ezop gtYadB}"
    bxAphg "rDijJBDUrJ.wdMvzMvm-lwIAE" 0 "sDfBhTJO: \{ezop sDfBhTJO}"

export
lFyyqrymKaFiQzrPtHrTNiyGVeLd : List (Name, Count, List Name) -> Elab Unit
lFyyqrymKaFiQzrPtHrTNiyGVeLd = vxEsogCIk $ \(v, t, rj) => tGnnJOliZKRsjjsVNdmnTlySP v t rj
