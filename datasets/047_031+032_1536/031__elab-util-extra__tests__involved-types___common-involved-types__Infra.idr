module Infra

import public Language.Reflection.Compat.TypeInfo

export
printInvolvedTypesVerdict : Name -> Count -> List Name -> Elab Unit
printInvolvedTypesVerdict tyName minRig expected = do
  logMsg "deptycheck.involved-types" 0 "given type: \{show tyName}"
  invTys <- allInvolvedTypes minRig !(getInfo' tyName)
  let invTys   = sortBy (comparing show) $ invTys <&> name
  expected <- for expected $ map TypeInfo.name . getInfo'
  let expected = sortBy (comparing show) expected
  when (invTys /= expected) $ do
    logMsg "deptycheck.involved-types" 0 "-------- !!! --------"
    logMsg "deptycheck.involved-types" 0 "found   : \{show invTys}"
    logMsg "deptycheck.involved-types" 0 "expected: \{show expected}"

export
printAllInvolvedTypesVerdict : List (Name, Count, List Name) -> Elab Unit
printAllInvolvedTypesVerdict = traverse_ $ \(n, r, ns) => printInvolvedTypesVerdict n r ns
