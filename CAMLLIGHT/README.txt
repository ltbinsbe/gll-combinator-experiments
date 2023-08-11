
Caml Light parser, grammar taken from: https://caml.inria.fr/pub/docs/manual-caml-light/

LANGUAGE EXTENSIONS
see: https://caml.inria.fr/pub/docs/manual-caml-light/node4.html

LANGUAGE DEVIATIONS
#1: "not" as prefix-operator and keyword
#2: "**" as keyword
#3: Capitalised identifiers are reserved for constructors
      - "true" and "false" are builtin constant constructors
          added to `cconstr` as keywords
#4: add [||] as builtin constant constructor
#5: removed expr ::= ident (redundant)
#6: "mod" as a keyword
#7: removed [] from pattern (already covered by constant)
#8: start a simple matching with an optional "|"

PARSER EVALUATION

inputs/*_camlc.ml:
  test programs obtained by concatenating several combinations of files
  taken from https://github.com/FBoisson/Camllight/tree/master/src/compiler

execs/flexible:       parser, flexible BNF combinators without lookahead
execs/flexible-look:  parser, flexible BNF combinators with lookahead
execs/binarised:      parser, flexible BNF combinators with binarisation and without lookahead
execs/binarised-look: parser, flexible BNF combinators with binarisation and with lookahead
execs/fungll:         parser, flexible FUN-GLL combinators without lookahead and without grammar generation

built on Ubuntu 20.04 with GHC 9.2.8

===
REPRODUCE DATA
===
last performed on 24/06/2023
NB. The lexicalisation phase produces a slightly different number of tokens since 10/08/2018

0) Fetching dependencies

   cabal get /local/path/dist-newbuild/sdist/fungll-combinators-remco-0.4.1.1.tar.gz
   cabal configure

The first command uses a locally installed version of the mentioned package and fetches into the current build environment.

1) Getting the "flexible+" data

Make sure that in src/Parser.hs:
  * line 7 is not commented out   (import GLL.Combinators.Interface ...)
  * line 8 is commented out       (import GLL.Combinators.BinaryInterface ...)
  * line 9 is commented out       (import GLL.ParserCombinators ...)
  * line 10 is commented out      (import GLL.ParserCombinatorsLookahead ...)

Make sure that in src/Main.hs:
  * line 9  is not commented out  (import GLL.Combinators ...)
  * line 10 is commented out      (import GLL.ParserCombinators ...)
  * line 11 is commented out      (import GLL.ParserCombinatorsLookahead ...)

  * line 32 is not commented out  (printParseDataWithOptions [] ...)
  * line 33 is commented out      (printParseDataWithOptions [noSelectTest] ...)

  cabal build && cp dist-newstyle/build/x86_64-linux/ghc-9.2.8/caml-light-reuse-0.1.0.0/x/rcl/build/rcl/rcl execs/flexible-look

Note that the part `x86_64-linux/ghc-9.2.8/` may dependent on your local setup.

  execs/flexible-look inputs/1097_camlc.ml
  execs/flexible-look inputs/2808_camlc.ml
  execs/flexible-look inputs/4531_camlc.ml
  execs/flexible-look inputs/8832_camlc.ml
  execs/flexible-look inputs/15900_camlc.ml
  execs/flexible-look inputs/28674_camlc.ml

The timings in the table are printed as "recognition time".

2) Getting the "flexible" data

Make sure that in src/Parser.hs:
  * line 7 is not commented out
  * line 8 is commented out
  * line 9 is commented out
  * line 10 is commented out

Make sure that in src/Main.hs:
  * line 9  is not commented out
  * line 10 is commented out
  * line 11 is commented out

  * line 32 is commented out
  * line 33 is not commented out

  cabal build && cp dist-newstyle/build/x86_64-linux/ghc-9.2.8/caml-light-reuse-0.1.0.0/x/rcl/build/rcl/rcl execs/flexible

  execs/flexible inputs/1097_camlc.ml
  execs/flexible inputs/2808_camlc.ml
  execs/flexible inputs/4531_camlc.ml
  execs/flexible inputs/8832_camlc.ml
  execs/flexible inputs/15900_camlc.ml
  execs/flexible inputs/28674_camlc.ml

The timings in the table are printed as "recognition time".

3) Getting the "binarised+" data

Make sure that in src/Parser.hs:
  * line 7 is commented out
  * line 8 is not commented out
  * line 9 is commented out
  * line 10 is commented out

Make sure that in src/Main.hs:
  * line 9  is not commented out
  * line 10 is commented out
  * line 11 is commented out

  * line 32 is not commented out
  * line 33 is commented out

  cabal build && cp dist-newstyle/build/x86_64-linux/ghc-9.2.8/caml-light-reuse-0.1.0.0/x/rcl/build/rcl/rcl execs/binarised-look

  execs/binarised-look inputs/1097_camlc.ml
  execs/binarised-look inputs/2808_camlc.ml
  execs/binarised-look inputs/4531_camlc.ml
  execs/binarised-look inputs/8832_camlc.ml
  execs/binarised-look inputs/15900_camlc.ml
  execs/binarised-look inputs/28674_camlc.ml

The timings in the table are printed as "recognition time".

4) Getting the "binarised" data

Make sure that in src/Parser.hs:
  * line 7 is commented out
  * line 8 is not commented out
  * line 9 is commented out
  * line 10 is commented out

Make sure that in src/Main.hs:
  * line 9  is not commented out
  * line 10 is commented out
  * line 11 is commented out

  * line 32 is commented out
  * line 33 is not commented out

  cabal build && cp dist-newstyle/build/x86_64-linux/ghc-9.2.8/caml-light-reuse-0.1.0.0/x/rcl/build/rcl/rcl execs/binarised


  execs/binarised inputs/1097_camlc.ml
  execs/binarised inputs/2808_camlc.ml
  execs/binarised inputs/4531_camlc.ml
  execs/binarised inputs/8832_camlc.ml
  execs/binarised inputs/15900_camlc.ml
  execs/binarised inputs/28674_camlc.ml

The timings in the table are printed as "recognition time".

5) Getting the "fungll" data

Make sure that in src/Parser.hs:
  * line 7  is commented out
  * line 8  is commented out
  * line 9  is not commented out
  * line 10 is commented out

Make sure that in src/Main.hs:
  * line 9  is commented out
  * line 10 is not commented out
  * line 11 is commented out

  * line 32 is not commented out
  * line 33 is commented out

  cabal build && cp dist-newstyle/build/x86_64-linux/ghc-9.2.8/caml-light-reuse-0.1.0.0/x/rcl/build/rcl/rcl execs/fungll

  execs/fungll inputs/1097_camlc.ml
  execs/fungll inputs/2808_camlc.ml
  execs/fungll inputs/4531_camlc.ml
  execs/fungll inputs/8832_camlc.ml
  execs/fungll inputs/15900_camlc.ml
  execs/fungll inputs/28674_camlc.ml

The timings in the table are printed as "recognition time".

6) Getting the "fungll-look" data

Make sure that in src/Parser.hs:
  * line 7  is commented out
  * line 8  is commented out
  * line 9  is commented out
  * line 10 is not commented out

Make sure that in src/Main.hs:
  * line 9  is commented out
  * line 10 is commented out
  * line 11 is not commented out

  * line 32 is not commented out
  * line 33 is commented out

  cabal build && cp dist-newstyle/build/x86_64-linux/ghc-9.2.8/caml-light-reuse-0.1.0.0/x/rcl/build/rcl/rcl execs/fungll-look

  execs/fungll-look inputs/1097_camlc.ml
  execs/fungll-look inputs/2808_camlc.ml
  execs/fungll-look inputs/4531_camlc.ml
  execs/fungll-look inputs/8832_camlc.ml
  execs/fungll-look inputs/15900_camlc.ml
  execs/fungll-look inputs/28674_camlc.ml

The timings in the table are printed as "recognition time".
