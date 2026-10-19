module Infra

import public Control.Monad.Identity
import public Control.Monad.Writer

import public Data.Alternative

import public Deriving.DepTyCheck.Util.DeepConsApp

%language ElabReflection

printDeepConsApp : List Name -> TTImp -> Elab Unit
printDeepConsApp freeNames tyExpr = do
  _ <- getNamesInfoInTypes' tyExpr
  logMsg         "deptycheck.deep-cons-app" 0 ""
  logMsg         "deptycheck.deep-cons-app" 0 "given free names:    \{show freeNames}"
  logSugaredTerm "deptycheck.deep-cons-app" 0 "original expression" tyExpr
  let Right tyExpr = resolveNamesUniquely (fromList freeNames) tyExpr
    | Left (n, alts) => logMsg "deptycheck.deep-cons-app" 0 "fail: name \{n} is not unique, alternatives: \{show $ Prelude.toList alts}"
  logSugaredTerm "deptycheck.deep-cons-app" 0 "resolved expression" tyExpr
  logMsg         "deptycheck.deep-cons-app" 0 "------------------------"
  let ((appliedNames ** bindExprF), []) = runWriter {w=List String} $ analyseDeepConsApp True (fromList freeNames) tyExpr
    | (_, errs) => logMsg "deptycheck.deep-cons-app" 0 "not a (deep) constructor application, reason: \{joinBy "; " errs}"
  let Nothing = foldAlt' appliedNames $ \case
                  (_, MustDecEqWith e) => Just "not a (deep) constructor application, match on non-cons expression `\{show e}`"
                  _                    => Nothing
    | Just err => logMsg "deptycheck.deep-cons-app" 0 err
  let appliedNames = fst <$> appliedNames.asVect
  logMsg         "deptycheck.deep-cons-app" 0 "applied names:   \{show appliedNames}"
  let bindExpr = bindExprF $ \idx => bindVar $ UN $ Basic $ show (index idx appliedNames) ++ show idx
  logSugaredTerm "deptycheck.deep-cons-app" 0 "bind expression" bindExpr

export
printDeepConsApps : Elab (List (List Name, TTImp)) -> Elab Unit
printDeepConsApps = (>>= traverse_ (uncurry printDeepConsApp))

--- Nice syntax ---

export infix 1 @@@

public export
(@@@) : b -> a -> (a, b)
y @@@ x = (x, y)
