
module Main where

import Print.Funcon (emptyModule)

import Control.Monad
import System.Environment
import System.FilePath
import System.Directory
import Data.Char (toUpper)
import Data.List (intercalate)
import Data.List.Split

main :: IO ()
main = getArgs >>= run top_level_dir

--dir_select :: [String] -> IO ()
--dir_select []           = putStrLn "Please provide me with an input directory"
--dir_select (inp:args)   = run inp args

top_level_dir = addTrailingPathSeparator $ "cbs" </> "Funcons" </> "Core" 
top_level_dirs = ["Abstractions", "Computations", "Values"]

-- input directory, additional arguments
run :: FilePath -> [String] -> IO ()
run idir args = do
    fpss <- forM top_level_dirs (find_cbs_files . (idir ++))
    let fps = concat fpss
    forM_ fps process
 where
    -- search recursively for .cbs files in some given subdirectory of the input
    find_cbs_files :: FilePath -> IO [FilePath]
    find_cbs_files "." = return []
    find_cbs_files ".." = return []
    find_cbs_files fp | hasExtension fp && ".cbs" == takeExtension fp = return [fp]
                      | hasExtension fp = return []
                      | otherwise = do  fps <- getDirectoryContents fp 
                                        fpss <- forM fps (find_cbs_files . (fp </>))
                                        return (concat fpss) 
                                
    -- process a .cbs file, by generating a .hs file
    process :: FilePath -> IO ()
    process cbs = do    createDirectoryIfMissing True (takeDirectory hs)
                        writeFile hs contents 
        where   contents    = emptyModule modName 
                hs          = foldr ((</>) . camelcase) ""  $ 
                                splitDirectories $ 
                                replace "cbs" "hs"  $
                                replaceExtension cbs "hs"
                modName     = intercalate "." $ 
                                map camelcase $ 
                                dropWhile (not . (`elem` roots)) $ 
                                splitDirectories (dropExtension cbs) -- drop "/"
                roots = ["Funcons", "Funcons-beta"]


camelcase :: String -> String
camelcase str = concatMap firstToCap (splitOneOf " -" str)
 where  firstToCap [] = []
        firstToCap (hd:tl) = (toUpper hd):tl

replace old new = intercalate new . splitOn old
