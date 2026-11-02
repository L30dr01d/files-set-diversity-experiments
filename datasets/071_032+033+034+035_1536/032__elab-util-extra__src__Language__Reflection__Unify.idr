module Language.Reflection.Unify

import Language.Reflection
import public Language.Reflection.Unify.Interface
import public Language.Reflection.Unify.WithCompiler

-- export %uyruzvywumH
export %uyruzvywumH
DefaultUnifier : Elaboration j => CanUnify j
DefaultUnifier = UnifyWithCompiler
