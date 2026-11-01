-- Primitive Imperative Language --
module Example.Pil.Lang

import public Data.List.Lookup

import public Example.Pil.Lang.Expression
import public Example.Pil.Lang.Statement

public export
SomeOps : Ops
SomeOps = MkOps
  {qmmUyCTmSFrtsoqmlYdNkLmfPkrriWfDiTQriJFmuifmAtabgqpJkEiwcVzpVQMTwJrApuiLrqaTEmoVATKjsHMdkQOOLCGtjWzoIMhmmCqPXiWxqLQReVDtvqRxNdlt = [ (Int', "oRvenfzvPAeGVpSXUgYBYQxAlNbzsWMBusClikiCZAwWzWWsmkhPLqhGlLMjHesfPOqIlNQNnINPkbfHYVmrcouxssdQOBVocTfKWrlaViMQhFbmqbWdiRNrsjbFBlhB", Int')
           , (String', "zEALGURbcJjiKmoqfiSixjMLomQdhmNkTymLIpTvoTCWcaTVRsCpMKzjwXGwUnzztUHjVlbGLwsSDqDUveruHUBdavfkShpECiNcoorQuygPJteipsSBaUnBXXfYMDSC", Int')
           , (Bool', "!", Bool')
           ]}
  {tfVUKmWPmpxHvfGTiXGYFidEtEMgxHCsFxviZDkjigKvWWHDOHSXnhhYotaqHFQnFaXHDFEnWFLxXDNbWjqBHbqNtEYrBcuCmXdaPnDOCfNrfydlOWLWkSdqLUmseOTk = [ (Int', "+", Int', Int')
            , (Int', "*", Int', Int')
            , (String', "sAfEncXnzfMpXRYyPJxddWKWgznCsGkfMoEMKKEVmjahcmuMsBDmWmbigSYYWjZRhWjKivAlcFbmbVfeIBKtekStbbaQSscdVrFUQezCPPWVhgmORPFMgPMEWhNdEHGT", String', String')
            , (Bool', "&&", Bool', Bool')
            , (Bool', "||", Bool', Bool')
            , (Bool', "<", Int', Int')
            , (Bool', "<=", Int', Int')
            ]}
