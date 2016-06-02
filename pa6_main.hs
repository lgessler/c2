-- Programming Languages, Compiler Practiucm
-- CS 4610, University of Virginia
-- Programming Assignment 6
-- Anish Tondwalkar
-- Theo Gutman-Solo
import Read
import AST

import Data.List (isPrefixOf)

import System.Environment (getArgs)

splitOn :: Eq a => [a] -> [a] -> [[a]]
splitOn []    _  = error "splitOn: empty delimiter"
splitOn delim xs = loop xs
    where loop [] = [[]]
          loop xs | delim `isPrefixOf` xs = [] : splitOn delim (drop len xs)
          loop (x:xs) = let (y:ys) = splitOn delim xs
                         in (x:y) : ys
          len = length delim

--formatting
main :: IO ()
main = do file <- head <$> getArgs
          theast@(AST (Maps c i p@(ParentMap pmap),_)) <- formatcontent . lines <$> readFile file
          writeFile ((head $ splitOn "." file)++".cl-asm") ""
