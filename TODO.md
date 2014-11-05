TODO
====

Functionality
-------------
* Support for case analysis
* Support for extensionality

Implementation Details
----------------------
* Use parseDecl from haskell-src-exts to parse datatype declarations, infix
  declarations (instead of declare_sym). This should yield a single parsec
  parser replacing dataParser, symParser and funParser.
* more pervasive use of state transformer with Env?

