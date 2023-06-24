
module Main where

import Lexer
import Parser
import Concrete


--import GLL.Combinators 
import GLL.ParserCombinators


import Control.Monad
import Data.List
import System.Environment

main :: IO()
main = getArgs >>= selectFile

selectFile :: [String] -> IO ()
selectFile args = 
  case filter (isSuffixOf ".ml") args of
    []          -> putStrLn "Please provide an .ml file"
    (_:(_:_))   -> putStrLn "Please provide a single .ml file"
    [file]      -> run file (filter (not . isSuffixOf ".ml") args)

run :: FilePath -> [String] -> IO ()
run fp args = do
  ml_contents <- readFile fp
  let lexRes :: [Token]
      lexRes = cl_lexer ml_contents
  printParseDataWithOptions [] [] pModule lexRes 
--  printParseDataWithOptions [noSelectTest] [] pModule lexRes 

