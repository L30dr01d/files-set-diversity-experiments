-- Primitive Imperative Language --
module Example.Pil.Lang

import public Data.List.Lookup

import public Example.Pil.Lang.Expression
import public Example.Pil.Lang.Statement

public export
SomeOps : Ops
SomeOps = MkOps
  {vwczkxbcXqvGvegpRlgrsxZeYzlsbVqwnvEXRgAAhmNlbGlcJarjOXwsxDRdOpfSHGPQhetOITYfOkxMGxAfQQEQPKJyBshgcsdKmjjJMOZizWniVmnbLqyOTZvQUgBd = [ (Int', "cPcANHtmKxmdYksVLUAclFjtKmFfQjhwnxzbmmPetubJaWcqUmgKuMJcFnHmRUOIZYhXYyVSddjwuOtJaxMFXwoioaDtkrBqgYyFznjOJTkQzybnLgGqCdibqSauIUXf", Int')
           , (String', "aIOSzywcwPmpfRtFqiorMNxrVYjcGhpTIDqbBYnOMOdUMSCtIUnLXSkpZdAAMqxgAuiLOJfJJPheALzxmjxjOcSkWLLYCQeJVNgNTwhAEZzIpbpOxrLFOpyQGdbDhIIr", Int')
           , (Bool', "!", Bool')
           ]}
  {anNefzuJlgoxaAPwjwKOLYlXybFdKqVzagNYZGzlWwdnrXvHaFvAxvXlVcpbOXHItoltZJXkNLqRXZunIksUBMHVFatqXZGtPWNlkMtkfsrmzzVMxeHxrSAICRVEYGhu = [ (Int', "+", Int', Int')
            , (Int', "*", Int', Int')
            , (String', "czdRoyDYTyFHqctiqtBdgmuCCqjqIiooFcqjpgtBBVbvKlPZvJZLeLrKgcObpzCxpivsSohEJlirpwIsgeSAGRkbdZbTShqBLuYrBIFflUlPWJDAYFkFryFuSkfUflZE", String', String')
            , (Bool', "&&", Bool', Bool')
            , (Bool', "||", Bool', Bool')
            , (Bool', "<", Int', Int')
            , (Bool', "<=", Int', Int')
            ]}
