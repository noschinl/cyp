module Test.Info2.Cyp.Util
    ( Err
    , debug
    , err
    , errStr
    , errCtxt
    , errCtxtStr
    , indent
    , eitherToErr
    )
where

import Text.PrettyPrint (Doc, ($+$), empty, nest, text)

{- Error handling combinators ---------------------------------------}

type Err a = Either Doc a

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
eitherToErr (Left x) = err $ foldr ($+$) empty (map text $lines $ show x)
eitherToErr (Right x) = Right x

debug :: Doc -> Doc
--debug = mempty
debug = id
