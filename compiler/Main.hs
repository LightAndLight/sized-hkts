module Main where

import qualified Data.Text as Text (pack)
import qualified Data.Text.IO as Text (readFile)
import qualified Data.Text.Lazy.IO as Lazy
import System.Environment (getArgs)
import System.Exit (exitFailure, exitSuccess)

import Codegen.C (prettyCDecls)
import Compile (parseAndCompile)

main :: IO ()
main = do
  file:_ <- getArgs
  contents <- Text.readFile file
  case parseAndCompile (Text.pack file) contents of
    Left err -> do
      Lazy.putStrLn err
      exitFailure
    Right res -> do
      print $ prettyCDecls res
      exitSuccess
