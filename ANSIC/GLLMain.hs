{-# LANGUAGE StandaloneDeriving #-}

module Main where

import GLLCombParser 

import Control.Monad
import Control.Arrow
import Data.Char
import Data.List
import System.Environment

main =  do  args <- getArgs
            case args of
              []    -> putStrLn "Please provide me with an input file"
              f:_   -> do   readFile f >>= 
                                (artLex >>> parse)

artLex :: String -> [Token]
artLex str = artLex' str
 where
    artLex' [] = []
    artLex' str@(c:cs) | isSpace c = artLex' $ dropWhile isSpace cs 
                       | otherwise = let (tstr,rest) = span (not . isSpace) str
                                      in Token tstr (Just tstr) : artLex' rest
