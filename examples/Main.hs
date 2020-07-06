module Main where

import Control.Monad (when)
import Data.Foldable (for_)
import qualified Data.Text as Text (pack)
import qualified Data.Text.IO as Text (readFile)
import qualified Data.Text.Lazy.IO as Lazy (writeFile)
import qualified System.Directory as Directory
import System.FilePath ((<.>))
import qualified System.FilePath as FilePath
import qualified Text.PrettyPrint.Leijen.Text as Pretty

import qualified Codegen.C as C
import qualified Compile

main :: IO ()
main =
  Directory.withCurrentDirectory "examples" $ do
    files <- Directory.listDirectory "."
    for_ files $ \file ->
      when (FilePath.takeExtension file == ".src") $ do
        contents <- Text.readFile file
        let
          output =
            case Compile.parseAndCompile (Text.pack file) contents of
              Left err -> err
              Right res -> Pretty.displayT $ Pretty.renderPretty 1.0 100 (C.prettyCDecls res)
        Lazy.writeFile (FilePath.dropExtension file <.> "out") output
