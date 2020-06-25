{-# language TypeApplications #-}
module Main where

import qualified Data.Maybe as Maybe
import Data.Text (Text)
import GHCJS.Foreign.Callback (Callback, asyncCallback2)
import GHCJS.Marshal (fromJSVal)
import GHCJS.Types (JSVal)
import Reflex.Dom (mainWidgetInElementById)

import Widget (widget)

foreign import javascript unsafe "widget_ = $1"
  setWidgetCallback :: Callback (JSVal -> JSVal -> IO ()) -> IO ()

main :: IO ()
main = do
  callback <- asyncCallback2 $ \jv1 jv2 -> do
    elId <- Maybe.fromJust <$> fromJSVal @Text jv1
    input <- Maybe.fromJust <$> fromJSVal @Text jv2
    mainWidgetInElementById elId (widget input)
  setWidgetCallback callback
