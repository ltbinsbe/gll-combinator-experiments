module Main where

import Parsing.Lexer (lexer)
import Parsing.Spec (parser)
import Simplify.ConcreteToAbstract (cs2as)
import Simplify.Simplifier (simplifier)
import Simplify.CoreToTarget (core2target)
import Simplify.LiftStrictness (lift_strictness)
import Simplify.TargetToFunconModules (target2fmodule)
import Print.HaskellModule (cbs2module)
--import Print.JavaClasses (cbs2classes)
--import Print.Ascii (cbs2ascii)
import Types.FunconModule (FunconModule)

import CCO.Component (Component, ioRun)

import Control.Monad (when)
import Data.List (isPrefixOf)
import Control.Arrow ((>>>))
import System.Environment (getArgs)

main = do   all_args <- getArgs
            let (options,args) = (filter pred all_args, filter (not . pred) all_args)
                  where pred = isPrefixOf "--"
            case args of
                [cbsf]             -> run cbsf Nothing Nothing options
                [cbsf,srcdir]      -> run cbsf (Just srcdir) Nothing options
                [cbsf,srcdir,lang] -> run cbsf (Just srcdir) (Just lang) options
                _       ->  putStrLn $ 
                   "version CBS-beta\n\
                    \usage: cbsc <CBS-PATH> <SRC-DIR> <LANG>\n\
                    \CBS-PATH: path to the .cbs file\n\
                    \            for which code is to be generated.\n\
                    \            The file should be within a directory named \"Funcons\".\n\
                    \SRC-DIR: the source-directory in which the code is to be generated.\n\
                    \LANG: the language for which the .cbs file contains a specification.\n"

run cbsfile srcdir lang options = do
    cbs_contents <- readFile cbsfile
    let core2target' 
          | "--generate-congruences" `elem` options = core2target >>> lift_strictness
          | otherwise                               = core2target
    target <- ioRun (lexer >>> parser)  cbs_contents
    target `seq` return ()
 where pholder = any (== "--generate-unspecified-funcons") options
   
cbs2 :: [String] -> FilePath -> Maybe FilePath -> Maybe String -> 
          CCO.Component.Component FunconModule (Maybe (IO ()))
cbs2 options  {-| "--java" `elem` options   = cbs2classes
              | "--ascii" `elem` options  = cbs2ascii
              | otherwise -}                = cbs2module

