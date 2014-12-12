module Test.Info2.Cyp.Util
    ( Err
    , debug
    , err
    , errStr
    , errCtxt
    , errCtxtStr
    , indent
    , eitherToErr
    , renderSrcExtsFail
    )
where

import Data.Monoid (mempty)
import Language.Haskell.Exts (SrcLoc (..), ParseResult (..))
import Text.PrettyPrint (Doc, (<>), (<+>), ($+$), colon, empty, int, nest, text)

type Err = Either Doc

err :: Doc -> Err a
err = Left

errStr :: String -> Err a
errStr = Left . text

errCtxt :: Doc -> Err a -> Err a
errCtxt d1 (Left d2) = Left $ indent d1 d2
errCtxt _ x = x

errCtxtStr :: String -> Err a -> Err a
errCtxtStr = errCtxt . text

indent :: Doc -> Doc -> Doc
indent d1 d2 = d1 $+$ nest 4 d2

eitherToErr :: Show a => Either a b -> Err b
eitherToErr (Left x) = err $ foldr ($+$) empty (map text $ lines $ show x)
eitherToErr (Right x) = Right x

debug :: Doc -> Doc
--debug = mempty
debug = id

renderSrcExtsFail :: String -> ParseResult a -> Doc
renderSrcExtsFail _ (ParseOk _) = mempty
renderSrcExtsFail typ (ParseFailed (SrcLoc _ _ col) msg) =
    (text "Failed to parse" <+> text typ <+> text "at position" <+> int col <> colon)
    `indent` text msg
