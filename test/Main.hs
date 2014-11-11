import Test.Info2.Cyp.Tasty
import Test.Tasty

main :: IO ()
main = do
  tree <- findTests "test-data"
  defaultMain tree
