
module Shared where

import Data.List (nub)

type Ident  = String

type Op         = String
operator_names :: [Op]

operator_names  = nub (infix_ops ++ prefix_ops)
infix_ops       = [ "+", "*" , "/" , "mod" , "+."  , "*.", "/.", "-", "-."
                  , "@", "^"  , "!" , ":=", "="   , "<>"  , "==", "!="
                  , "<", "<=" , ">" , ">=", "<."  , "<=." , ">.", ">=."
                  , "**" {- DEVIATION #2 -}
                  ]
prefix_ops      = [ "-", "-.", "!"
                  , "not" {- DEVIATION #1 -}
                  ]

data Assoc  = LAssoc | RAssoc | NA
data Fixity = PreFix | InFix
type Prec   = Int

ops_priorities = [
    [ ("-", PreFix, NA), ("-.", PreFix, NA) ]
  , [ ("**", InFix, RAssoc) ]
  , [ ("mod", InFix, LAssoc) ]
  , [ ("*", InFix, LAssoc), ("*.", InFix, LAssoc)
     ,("/", InFix, LAssoc), ("/.", InFix, LAssoc) ]
  , [ ("+", InFix, LAssoc), ("+.", InFix, LAssoc)
     ,("-", InFix, LAssoc), ("-.", InFix, LAssoc) ]
  , [ ("::", InFix, RAssoc) ]
  , [ ("@", InFix, RAssoc), ("^", InFix, RAssoc) ]
  , [ ("=",InFix,LAssoc),("<>",InFix,LAssoc),("==",InFix,LAssoc),("!=", InFix,LAssoc)
     ,("<",InFix,LAssoc),("<.",InFix,LAssoc),("<=",InFix,LAssoc),("<=.",InFix,LAssoc)
     ,(">",InFix,LAssoc),(">.",InFix,LAssoc),(">=",InFix,LAssoc),(">=.",InFix,LAssoc)]
  , [ ("not", PreFix, NA) ]
  ] 
