import System.Environment (getArgs)
import System.Exit        (exitFailure)

import Eazy.Lex   (Token, mkPosToken)
import Eazy.Par   (pProgram, myLexer)
import Eazy.Print (Print, printTree)
import TypeChecker (typeCheck)
import Prologue (enrich)
import Interpreter (interpret, evalMain)
import Control.Monad.Trans.State (runStateT)

runFile :: FilePath -> IO ()
runFile f = readFile f >>= runProgram

runProgram :: String -> IO ()
runProgram ts = let 
  result = do
    parsed      <- pProgram $ myLexer ts
    typeChecked <- typeCheck $ enrich parsed
    interpreted <- interpret typeChecked
    evalMain interpreted
  in case result of
    Left err -> do
      putStrLn err
      exitFailure
    Right rt -> print rt

main :: IO ()
main = do
  args <- getArgs
  case args of
    []         -> getContents >>= runProgram
    filename   -> mapM_ runFile filename
