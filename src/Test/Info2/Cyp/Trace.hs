module Test.Info2.Cyp.Trace
    ( tracePretty
    , tracePrettyA
    , tracePrettyA'
    , tracePrettyF
    )
where

import Debug.Trace
import Text.Show.Pretty (ppShow)


tracePretty :: Show a => a -> b -> b
tracePretty = trace . ppShow

tracePrettyA :: Show a => a -> a
tracePrettyA x = tracePretty x x

tracePrettyA' :: Show a => String -> a -> a
tracePrettyA' s x = trace (s ++ "\n" ++ ppShow x) x

tracePrettyF :: Show b => (a -> b) -> a -> a
tracePrettyF f x = tracePretty (f x) x
