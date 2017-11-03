{-# language LambdaCase #-}
{-# language TypeApplications #-}

module Main where

import Simplicity

-- import ConCat.Category hiding (Category)
import ConCat.AltCat (toCcc)
import ConCat.Syntactic (Syn, render)
import ConCat.Misc (R, sqr)

runSyn :: Syn a b -> IO ()
runSyn syn = putStrLn $ render syn

runSimplicity :: Term a b -> IO ()
runSimplicity tm = putStrLn $ show tm

main :: IO ()
main = do
  putStrLn ""
  -- runSyn $ toCcc $ \x -> x
  -- runSyn $ toCcc $ \x -> x + (5 :: Int)
  -- runSyn $ toCcc $ (==) @Int
  -- runSyn $ toCcc $ \a b c -> b c
  -- runSyn $ toCcc $ \(a, b) -> b a
  -- runSyn $ toCcc $ sqr @R

  runSimplicity $ toCcc $ \x -> x
  runSimplicity $ toCcc $ \(x, y) -> y
  runSimplicity $ toCcc $ \(x, y) -> (y, x)
  runSimplicity $ toCcc $ \(x, y, z) -> case z of
    True -> x
    False -> y

  -- runSimplicity $ toCcc $ \a b c -> (a, b, c)
