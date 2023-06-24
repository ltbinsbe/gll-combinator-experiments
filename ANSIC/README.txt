
This grammar is a transcription of the rules in section A13 of 'The C Programming Language' by Brian W Kernighan and Dennis M Ritchie, second edition 1988 (Prentice Hall, ISBN 0-13-110362-8). 

inputs/*_gtb.toc: input strings obtained by concatenating several combinations
                  of source files taken from a `Grammar Tool Box' 
                  and then tokenised by a separate lexer
inputs/*_rdp.toc: input strings obtained by concatenating several combinations
                  of source files taken from a `Recursive Descent Parser generator'
                  and then tokenised by a separate lexer
              
execs/flexible:       parser, flexible BNF combinators without lookahead
execs/flexible-look:  parser, flexible BNF combinators with lookahead
execs/binarised:      parser, flexible BNF combinators with binarisation and without lookahead
execs/binarised-look: parser, flexible BNF combinators with binarisation and with lookahead
execs/fungll:         parser, flexible FUN-GLL combinators without lookahead and without grammar generation

built on Ubuntu 20.04 with GHC 9.2.8

===
REPRODUCE DATA
===
last performed on 24/6/2023

1) Getting the "flexible+" data

Make sure that in GLLCombParser.hs:

  * line 2    is commented out      (import GLL.Combinators.BinaryInterface ...)
  * line 3    is not commented out  (import GLL.Combinators.Interface ...)
  * line 4    is commented out      (import GLL.ParserCombinators ...)
  * line 537  is not commented out  (Lib.printParseDataWithOptions [] ...)
  * line 538  is commented out      (Lib.printParseDataWithOptions [noSelect...)

  ghc -o execs/flexible-look GLLMain.hs -package gll

Running the following commands should give timings consistent with ../20180708_data.xls (row flexible+)

  execs/flexible-look inputs/1515_rdp.tok
  execs/flexible-look inputs/8411_rdp.tok
  execs/flexible-look inputs/15589_rdp.tok
  execs/flexible-look inputs/26551_rdp.tok
  execs/flexible-look inputs/36827_gtb.tok

The timings in the table are printed as "recognition time".

2) Getting the "flexible" data

Make sure that in GLLCombParser.hs

  * line 2    is commented out
  * line 3    is not commented out
  * line 4    is commented out 
  * line 537  is commented out 
  * line 538  is not commented out

  ghc -o execs/flexible GLLMain.hs -package gll

Running the following commands should give timings consistent with ../20180708_data.xls (row flexible)

  execs/flexible inputs/1515_rdp.tok
  execs/flexible inputs/8411_rdp.tok
  execs/flexible inputs/15589_rdp.tok
  execs/flexible inputs/26551_rdp.tok
  execs/flexible inputs/36827_gtb.tok

The timings in the table are printed as "recognition time".

3) Getting the "binarised" data

Make sure that in GLLCombParser.hs

  * line 2    is not commented out
  * line 3    is commented out
  * line 4    is commented out
  * line 537  is commented out 
  * line 538  is not commented out

  ghc -o execs/binarised GLLMain.hs -package gll

Running the following commands should give timings consistent with ../20180708_data.xls (row binarised)

  execs/binarised inputs/1515_rdp.tok
  execs/binarised inputs/8411_rdp.tok
  execs/binarised inputs/15589_rdp.tok
  execs/binarised inputs/26551_rdp.tok
  execs/binarised inputs/36827_gtb.tok

The timings in the table are printed as "recognition time".

4) Getting the "binarised+" data

 Make sure that in GLLCombParser.hs

  * line 2    is not commented out
  * line 3    is commented out
  * line 4    is commented out 
  * line 537  is not commented out 
  * line 538  is commented out

  ghc -o execs/binarised-look GLLMain.hs -package gll

Running the following commands should give timings consistent with ../20180708_data.xls (row binarised+)

  execs/binarised-look inputs/1515_rdp.tok
  execs/binarised-look inputs/8411_rdp.tok
  execs/binarised-look inputs/15589_rdp.tok
  execs/binarised-look inputs/26551_rdp.tok
  execs/binarised-look inputs/36827_gtb.tok

The timings in the table are printed as "recognition time".

5) Getting the "fungll" data

Make sure that in GLLCombParser.hs:

  * line 2    is commented out     
  * line 3    is commented out     
  * line 4    is not commented out 
  * line 537  is not commented out 
  * line 538  is commented out     

  ghc -o execs/fungll GLLMain.hs -package fungll-combinators

Running the following commands should produce timings 

  execs/fungll inputs/1515_rdp.tok
  execs/fungll inputs/8411_rdp.tok
  execs/fungll inputs/15589_rdp.tok
  execs/fungll inputs/26551_rdp.tok
  execs/fungll inputs/36827_gtb.tok

The timings in the table are printed as "recognition time".


