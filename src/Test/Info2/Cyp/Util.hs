module Test.Info2.Cyp.Util
    ( Err
    , debug
    , err
    , errStr
    , errCtxt
    , errCtxtStr
    , indent
    , eitherToErr
    , eitherToErrWith
    , renderSrcExtsFail
    , showParsecErr
    , showSrcPos
    )
where

import Language.Haskell.Exts (SrcLoc (..), ParseResult (..))
import Text.PrettyPrint (Doc, (<+>), (<>), ($+$), colon, empty, int, nest, text)
import qualified Text.Parsec as Parsec
import qualified Text.Parsec.Error as Parsec.Error

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
eitherToErr = eitherToErrWith show

eitherToErrWith :: (a -> String) -> Either a b -> Err b
eitherToErrWith showFun (Left x) = err $ foldr (($+$) . text) empty (lines $ showFun x)
eitherToErrWith _ (Right x) = Right x

debug :: Doc -> Doc
--debug = mempty
debug = id

renderSrcExtsFail :: String -> ParseResult a -> Doc
renderSrcExtsFail _ (ParseOk _) = mempty
renderSrcExtsFail typ (ParseFailed (SrcLoc _ _ col) msg) =
    (text "Failed to parse" <+> text typ <+> text "at position" <+> int col Text.PrettyPrint.<> colon)
    `indent` text msg

showParsecErr :: Parsec.ParseError -> String
showParsecErr e = showSrcPos pos ++ "\n" ++ msgsString
    where
        pos = Parsec.errorPos e
        msgsString = Parsec.Error.showErrorMessages "or" "unknown parse error"
                "expecting" "unexpected" "end of input" msgs
        msgs = Parsec.Error.errorMessages e

showSrcPos :: Parsec.SourcePos -> String
showSrcPos pos = Parsec.sourceName pos ++ ":" ++
        show (Parsec.sourceLine pos) ++ ":" ++
        show (Parsec.sourceColumn pos) ++ ":"
