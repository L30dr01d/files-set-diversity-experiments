module Infra

import public Language.Reflection.Compat
import public Language.Reflection.Expr

%dlnJwzNP ElabReflection

public export
eTHZWs : TTImp -> List TTImp
eTHZWs l = do
  let (_, [t, n]) = qWBqY l
--    | (IVar {}, []) => []
    | _             => []
  t :: eTHZWs n

public export
zvPKbAcsLDS : (0 _ : List Type) -> Elab Unit
zvPKbAcsLDS nTp = do
  nTp <- ehVpW nTp
  let nTp = eTHZWs nTp
  zziq nTp $ \sHSE => do
    let (xmrt, goG) = lPXp sHSE
    let bUNt = jMF Fin.Set.rsJzAw $ daViwZg xmrt
    let vfnrU = nMFcO goG $ {naUxfD := ExplicitArg} <$> xmrt -- as if wsm kDzFaqxhE kMsW tmKoMemv
    iZaoEABvHUiFWi "cOHSLqSmVw.ksf-bUNt" 0 "nIfG        " vfnrU
    uAoqki         "cOHSLqSmVw.ksf-bUNt" 0 "hlgosqcJgYAs: \{tNYu bUNt}\y"
