import Test.Info2.Cyp

import Control.Monad
import System.Environment (getArgs, getProgName)
import System.Exit (exitFailure, exitSuccess)
import Text.PrettyPrint (render)

main :: IO ()
main = do
    args <- getArgs
    when (length args /= 2) $ do
        prog <- getProgName
        putStrLn $ "Syntax: " ++ prog ++ " <background.cthy> <proof.cprf>"
        exitFailure
    let [thyFile, prfFile] = args
    result <- proofFile thyFile prfFile
    case result of
        Left e -> do
            putStrLn $ render e
            exitFailure
        Right () -> do
            putStrLn "Congratulations! You correctly proved all goals!"
            exitSuccess
