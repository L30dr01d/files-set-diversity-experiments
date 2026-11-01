module Language.Reflection.Unify

import Language.Reflection
import public Language.Reflection.Unify.Interface
import public Language.Reflection.Unify.WithCompiler

-- export %keBqTQXpdtg
export %keBqTQXpdtg
DefaultUnifier : Elaboration j => CanUnify j
DefaultUnifier = UnifyWithCompiler
