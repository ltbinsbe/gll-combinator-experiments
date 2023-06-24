module Main where

import IML.Tools as IML
import qualified IML.Trans.UniChain
import qualified IML.Trans.TransChain

import Parsing.Lexer (lexer)
import Parsing.Spec (parser)
import Print.Util (hsmodNameFromPath)
import Simplify.ConcreteToAbstract (cs2as)
import Simplify.Simplifier (simplifier)
import Simplify.CoreToTarget (core2target)
import Simplify.TargetToIML (target2iml)
import Simplify.LiftStrictness (lift_strictness)
import Types.ConcreteSyntax (MetaSpec(..))
import Types.TargetAbstractSyntax (CBSFile(..))

import CCO.Component (ioRun)

import Control.Monad (forM_)
import Control.Arrow ((>>>))
import System.Environment (getArgs)
import System.FilePath
import System.Directory (createDirectoryIfMissing)

import Data.List (intercalate,isPrefixOf)
import qualified Data.Map as M

main = do   all_args <- getArgs
            let (options,args) = (filter pred all_args, filter (not . pred) all_args)
                  where pred = isPrefixOf "--"
            case args of
                [cbsf, dir, lang] -> run cbsf dir lang options
                _       ->  putStrLn $ 
                   "usage: cbs2imlc <CBS-PATH> <PATH> <LANG> <OPTIONS> \n\
                    \CBS-PATH: path to the .cbs file\n\
                    \            for which code is to be generated.\n\
                    \            The file should be within a directory named \"Funcons\".\n\
                    \PATH: path to a directory to generate the file\n\
                    \             where to produced IML program should be generated"

run cbsfile dir lang options = do
    cbs_contents <- readFile cbsfile
    let core2target' | "--generate-congruences" `elem` options =  
                        core2target >>> lift_strictness
                     | otherwise = core2target
    target <- ioRun (lexer >>> parser >>> cs2as True >>> simplifier 
                          >>> core2target') cbs_contents
    case () of
      ()  | "--data-only" `elem` options  -> printCSV target
          | "--siml" `elem` options       -> generateSIML target
          | otherwise                     -> 
              generate IML.Trans.TransChain.chain target

 where 
  generateSIML target = do 
    program <- IML.runComponentIO (IML.runOptions options) 
                (target2iml >>> IML.initRuleFormatChain
                   >>> IML.Trans.UniChain.chain) target
    printIML options simlfile program
    where simlfile = "/tmp" </> takeFileName (replaceExtension cbsfile ".siml")

  generate chain target = do 
    program <- IML.runComponentIO (IML.runOptions options) 
                    (target2iml >>> chain) target
    createDirectoryIfMissing True hsdir
    let hs_module = set_modname modname $
                      foldr add_import (generateHSmodule options program)
                                       (metadata target) 
    printHSmodule hsfile hs_module
   where  hsdir   = dir </> foldr (</>) "" ( init modname ) 
          modname = hsmodNameFromPath lang cbsfile
          hsfile  = hsdir </> last modname <.> ".hs"
          add_import (HS_Imports string) = add_direct_import string
 
  printCSV target = do 
    graphs <- IML.runComponentIO (IML.runOptions options) 
                    (target2iml >>> IML.Trans.TransChain.graph_chain) target
    forM_ (M.keys graphs) $ \(c,r) -> do 
      let mygraphs = maybe [] id (M.lookup (c,r) graphs)
          prefix = [c,r, show $ length mygraphs] 
          (sum,depth,suffix) = foldr op (0,0,[]) mygraphs
            where op g (s,d,acc) = (s',d',show g_nodes:show depth:acc)
                    where g_nodes = length (nodes g)
                          depth   = maximum (map length (paths g))
                          s'      = s + g_nodes
                          d'      | d >= depth = d
                                  | otherwise  = depth
      csLine (prefix ++ [show sum, show depth] ++ suffix) 
 

csLine :: [String] -> IO () 
csLine = putStrLn . intercalate "," 
    --printIML options simlf iml_program
