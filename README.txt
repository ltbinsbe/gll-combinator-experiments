===
AUTHORS
===
L. Thomas van Binsbergen <ltvanbinsbergen@acm.org>

===
SOFTWARE VERSIONS
===
All of the following tests are performed under
* Ubuntu 20.04
* GHC 9.2.8
* Cabal 3.6.2.0

===
CONTENTS
===

README.txt:         README file with installation instructions
ANSIC:              folder containing files necessary for ANSIC tests 
                    (see ANSIC/README.txt)
CAMLLIGHT:          folder containing files necessary for Caml Light tests
                    (see CAMLLIGHT/README.txt)
CBS:                folder containing files necessary for CBS tests
                    (see CBS/README.txt)

===
EVALUATION DATA
===

The following steps can be used to reproduce the evaluation data in the paper.
The actual numbers will vary, depending on machine set-up, but the trents discussed in the paper should be observable.

1) install `gll` and `fungll-combinators` libraries (included version number is latest tested version)
  
    cabal install gll-0.4.1.1
    cabal install fungll-combinators-0.4.1.1

2) produce experimental data

see ANSIC/README.txt
    CAMLLIGHT/README.txt
    CBS/README.txt
