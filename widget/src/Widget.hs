{-# language OverloadedStrings #-}
{-# language ScopedTypeVariables #-}
module Widget (widget) where

import Data.Text (Text)
import qualified Data.Text.Lazy as Lazy
import Reflex.Dom

import qualified Codegen.C as C
import qualified Compile

widget :: forall t m. DomBuilder t m => Text -> m ()
widget input = do
  te <- textAreaElement (def & textAreaElementConfig_initialValue .~ input)
  let dSourceCode = te ^. textAreaElement_value
  ePressedCompile <- dSourceCode button "Compile"
  let compile = Compile.parseAndCompile "interactive"
  dCompiledOutput :: Dynamic t (Either Lazy.Text C.CDecl) <-
    holdDyn (compile input) $
    compile <$> current dSourceCode <@ ePressedCompile
  dyn_ $ text . either Lazy.toStrict C.prettyCDecls <$> dCompiledOutput
