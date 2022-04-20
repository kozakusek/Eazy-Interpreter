import System.Environment (getArgs)
import System.Exit        (exitFailure)

import Eazy.Lex   (Token, mkPosToken)
import Eazy.Par   (pProgram, myLexer)
import Eazy.Print (Print, printTree)
import TypeChecker (typeCheck)
import Prologue (enrich)
import Interpreter (interpret, evalMain)
import Control.Monad.Trans.State (runStateT)
import Control.Monad.IO.Class (liftIO)

runFile :: FilePath -> IO ()
runFile f = readFile f >>= runProgram

runProgram :: String -> IO ()
runProgram ts = let
    result = do
        parsed <- enrich $ pProgram $ myLexer ts
        warns <- typeCheck parsed
        interpreted <- interpret parsed
        result <- evalMain interpreted
        return (result, warns)
    in case result of
        Left err -> do
            putStrLn err
            exitFailure
        Right (rt, msg) -> msg >> print rt

main :: IO ()
main = do
    args <- getArgs
    case args of
        []       -> getContents >>= runProgram
        filename -> mapM_ runFile filename
