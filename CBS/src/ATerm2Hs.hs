
module Main where

import Parsing.ATerm (aterm2cbs)
import Simplify.Simplifier (simplifier)
import Simplify.CoreToTarget (core2target)
import Simplify.TargetToFunconModules (target2fmodule)
import Print.HaskellModule (cbs2module)
import Print.JavaClasses (cbs2classes)
import Types.FunconModule (FunconModule)

import CCO.Component (Component, ioRun)
import CCO.Tree (parser, ATerm)

import Data.List (isPrefixOf)
import Control.Arrow ((>>>))
import System.Environment (getArgs)

main = do   all_args <- getArgs
            let (options,args) = (filter pred all_args, filter (not . pred) all_args)
                  where pred = isPrefixOf "--"
            case args of
                [aterm]             -> run aterm Nothing Nothing options
                [aterm,srcdir,lang] -> run aterm (Just srcdir) (Just lang) options
                _       ->  putStrLn $ 
                   "usage: aterm2hs <ATERM-PATH> <HS-DIR> <LANG>\n\
                    \CBS-PATH: to path to the .aterm file (generated from a .cbs file)\n\
                    \            for which a Haskell module is to be generated.\n\
                    \            The file should be within a directory name \"Funcons\".\n\
                    \HS-DIR: the source-directory for the Haskell module.\n\
                    \LANG: the language for which the .cbs file contains a specification."

run atermfile srcdir lang options = do
    aterm_contents <- readFile atermfile
    m_hs_contents <- ioRun (string2aterm >>> aterm2cbs pholder >>> simplifier 
                    >>> core2target >>> target2fmodule >>>
                         (cbs2 options) atermfile srcdir lang) aterm_contents
    case m_hs_contents of
        Nothing -> putStrLn "No funcons, types or entities to generate"
        Just make_hs_contents -> make_hs_contents
 where pholder = any (== "--generate-unspecified-funcons") options
   
cbs2 :: [String] -> FilePath -> Maybe FilePath -> Maybe String -> 
          Component FunconModule (Maybe (IO ()))
cbs2 options  | "--java" `elem` options = cbs2classes
              | otherwise               = cbs2module

string2aterm :: Component String ATerm
string2aterm = parser


