
CBS compiler (Van Binsbergen @ MODULARITY 2016)

inputs/*cbs: 
  test programs obtained by concatenating several combinations of files 
  https://plancomps.github.io/CBS-beta/Languages-beta/OCaml-Light/

execs/flexible:       parser, flexible BNF combinators
execs/flexible-look:  parser, flexible BNF combinators with lookahead
execs/binarised:      parser, flexible BNF combinators with binarisation
execs/binarised-look: parser, flexible BNF combinators with binarisation and lookahead

built on Ubuntu 14.04 with GHC 8.2.1

===
REPRODUCE DATA
===
last performed on 01/09/2018

0) Installing dependencies

To install, a local installation of `uu-cco` version `>= 0.1.0.6` is required, provided [here](https://github.com/ltbinsbe/uu-cco), taking the following steps:

1. download and unpack zip
2. enter folder `uu-cco` and run `cabal sdist`
3. within the `funcons-intgen` repository folder:  
`cabal get <UU-CCO/dist-newstyle/sdist/uu-cco-<VERSION>.tar.gz`  
where `<UU-CCO>` is the path to the `uu-cco` folder of the previous step and `<VERSION>` is the version of the package (`>= 0.1.0.6`)

After these steps, confirm the dependencies by executing
    
    cabal configure

1) Getting the "flexible+" data

Make sure that in src/Parsing/Combinators.hs:
  * line 5 is not commented out  (import GLL.Combinators.Interface ...)
  * line 6 is commented out      (import GLL.Combinators.BinaryInterface ...)
  * line 7 is commented out      (import GLL.ParserCombinators ...)

Make sure that in src/Parsing/Spec.hs:
  * line 16 is not commented out (parser = ... [strictBinarisation] ...)
  * line 17 is commented out     (parser = ... [noSelectTest,strictBinarisation] ...)
  * line 18 is commented out     (parser = ... [] ...)

  cabal build && cp dist-newstyle/build/x86_64-linux/ghc-9.2.8/funcons-intgen-0.2.0.0/x/cbsc/build/cbsc/cbsc execs/flexible-look

Note that the part `x86_64-linux/ghc-9.2.8/` may dependent on your local setup.

  execs/flexible-look inputs/2653_CL_12_Core_Library.cbs
  execs/flexible-look inputs/14824_ocamllight.cbs
  execs/flexible-look inputs/17593_ocamllight.cbs
  execs/flexible-look inputs/21162_ocamllight.cbs
  execs/flexible-look inputs/26016_ocamllight.cbs

The timings in the table are printed as "total time".

2) Getting the "flexible" data

Make sure that in src/Parsing/Combinators.hs:
  * line 5 is not commented out
  * line 6 is commented out
  * line 7 is commented out

Make sure that in src/Parsing/Spec.hs:
  * line 16 is commented out
  * line 17 is not commented out
  * line 18 is commented out

  cabal build && cp dist-newstyle/build/x86_64-linux/ghc-9.2.8/funcons-intgen-0.2.0.0/x/cbsc/build/cbsc/cbsc execs/flexible

  execs/flexible inputs/2653_CL_12_Core_Library.cbs
  execs/flexible inputs/14824_ocamllight.cbs
  execs/flexible inputs/17593_ocamllight.cbs
  execs/flexible inputs/21162_ocamllight.cbs
  execs/flexible inputs/26016_ocamllight.cbs

The timings in the table are printed as "total time".

3) Getting the "binarised+" data

Make sure that in src/Parsing/Combinators.hs:
  * line 5 is commented out
  * line 6 is not commented out
  * line 7 is commented out 

Make sure that in src/Parsing/Spec.hs:
  * line 16 is not commented out
  * line 17 is commented out
  * line 18 is commented out

  cabal build && cp cp dist-newstyle/build/x86_64-linux/ghc-9.2.8/funcons-intgen-0.2.0.0/x/cbsc/build/cbsc/cbsc execs/binarised-look

  execs/binarised-look inputs/2653_CL_12_Core_Library.cbs
  execs/binarised-look inputs/14824_ocamllight.cbs
  execs/binarised-look inputs/17593_ocamllight.cbs
  execs/binarised-look inputs/21162_ocamllight.cbs
  execs/binarised-look inputs/26016_ocamllight.cbs

The timings in the table are printed as "total time".

4) Getting the "binarised" data

Make sure that in src/Parsing/Combinators.hs:
  * line 5 is commented out
  * line 6 is not commented out
  * line 7 is commented out 

Make sure that in src/Parsing/Spec.hs:
  * line 16 is commented out
  * line 17 is not commented out
  * line 18 is commented out

  cabal build && cp dist-newstyle/build/x86_64-linux/ghc-9.2.8/funcons-intgen-0.2.0.0/x/cbsc/build/cbsc/cbsc execs/binarised

  execs/binarised inputs/2653_CL_12_Core_Library.cbs
  execs/binarised inputs/14824_ocamllight.cbs
  execs/binarised inputs/17593_ocamllight.cbs
  execs/binarised inputs/21162_ocamllight.cbs
  execs/binarised inputs/26016_ocamllight.cbs

The timings in the table are printed as "total time".

5) Getting the "fungll" data

Make sure that in src/Parsing/Combinators.hs:
  * line 5 is commented out
  * line 6 is commented out
  * line 7 is not commented out 

Make sure that in src/Parsing/Spec.hs:
  * line 16 is commented out
  * line 17 is commented out
  * line 18 is not commented out

  cabal build && cp dist-newstyle/build/x86_64-linux/ghc-9.2.8/funcons-intgen-0.2.0.0/x/cbsc/build/cbsc/cbsc execs/fungll

  execs/fungll inputs/2653_CL_12_Core_Library.cbs
  execs/fungll inputs/14824_ocamllight.cbs
  execs/fungll inputs/17593_ocamllight.cbs
  execs/fungll inputs/21162_ocamllight.cbs
  execs/fungll inputs/26016_ocamllight.cbs

The timings in the table are printed as "total time".


