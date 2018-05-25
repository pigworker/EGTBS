module Main where

seek :: String -> String
seek ('{':'-':'<':'-':'}':s) = "     " ++ hide s
seek (c : s) = c : seek s
seek [] = []

hide :: String -> String
hide ('{':'-':'>':'-':'}':s) = "     " ++ seek s
hide (c : s) = ' ' : hide s
hide [] = []

main :: IO ()
main = interact seek