{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE LambdaCase #-}

module Test.Info2.Cyp.Tasty (
  CypTest(..)
, findTests
) where

import Control.Applicative ((<$>))
import Data.List
import Data.Tagged (Tagged(..))
import Data.Typeable (Typeable)
import qualified Test.Info2.Cyp as Cyp
import Test.Info2.Cyp.Util
import Test.Tasty
import Test.Tasty.Providers
import Text.PrettyPrint (empty, render, text, ($+$))
import System.Directory
import System.FilePath


data CypTest = CypTest { theory :: FilePath
                       , proof :: FilePath
                       } deriving Typeable

instance IsTest CypTest where
  testOptions = Tagged []
  run _ t _ = either (testFailed . render) (const $ testPassed "Proof is valid") <$> Cyp.proofFile (theory t) (proof t)


data NegCypTest = NegCypTest FilePath CypTest deriving Typeable

instance IsTest NegCypTest where
  testOptions = Tagged []
  run _ (NegCypTest expected t) _ =
    Cyp.proofFile (theory t) (proof t) >>= \case
      Left failure -> do
        contents <- readFile expected
        let doc = foldr ($+$) empty $ map text $ lines contents
        return $
          if contents /= render failure then
            testFailed $ render $
              text "Proof is invalid as expected, but with the wrong error message" `indent`
                (text "Expected failure:" `indent` doc $+$ text "Actual failure:" `indent` failure)
          else
            testPassed "Proof is invalid as expected"
      Right () ->
        return $ testFailed "Proof is valid, but expected failure"

findTests :: FilePath -> IO TestTree
findTests path = do
  allPos <- findAll pos
  allNeg <- findAll neg
  return $ testGroup ("Tests for " ++ show path)
    [ testGroup "Valid proofs" $ map (mkPos pos) allPos
    , testGroup "Invalid proofs" $ map (mkNeg neg) allNeg
    ]
  where pos = path </> "pos"
        neg = path </> "neg"
        findAll path =
          filter (not . isPrefixOf ".") <$> getDirectoryContents path
        mkTest root item = CypTest { theory = root </> item </> "cthy", proof = root </> item </> "cprf" }
        mkNeg root item = singleTest item $ NegCypTest (root </> item </> "cout") $ mkTest root item
        mkPos root item = singleTest item $ mkTest root item
