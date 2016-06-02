-- Programming Languages, Compiler Practiucm
-- CS 4610, University of Virginia
-- Programming Assignment 6
-- Anish Tondwalkar
-- Theo Gutman-Solo
import Read
import GenCode
import Control.Applicative
import Control.Monad.State
import Compiler
import COOLASM
import IR
import AST
import Debug.Trace
import Data.List
import System.Environment (getArgs)
import CompilerFuncs

splitOn :: Eq a => [a] -> [a] -> [[a]]
splitOn []    _  = error "splitOn: empty delimiter"
splitOn delim xs = loop xs
    where loop [] = [[]]
          loop xs | delim `isPrefixOf` xs = [] : splitOn delim (drop len xs)
          loop (x:xs) = let (y:ys) = splitOn delim xs
                         in (x:y) : ys
          len = length delim

--formatting
main::IO ()
main = do file <- head <$> getArgs
          theast@(AST (Maps c i p@(ParentMap pmap),_)) <- formatcontent . lines <$> readFile file
          let myCompiler = emptyCompiler { topSortedClasses = topSortPmap p,
                                           classTags = genClassTags pmap (topSortPmap p),
                                           mthdOffsetTable = initOffSetTable i,
                                           pMap = pmap,
                                           cMap = c,
                                           iMap = i
                                         }
              thestate = (\x -> runState x myCompiler) $ compile theast in
              writeFile ((head $ splitOn "." file)++".cl-asm") (unlines . bigFriendlyButton $ snd thestate)

emptyCompiler :: CompilerState
emptyCompiler = CompilerState [] 0 0 (Raw "devnull") [] [] [] "" [] [] [] [] (ClassMap []) (ImpMap [])
