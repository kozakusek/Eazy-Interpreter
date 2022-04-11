import System.Environment (getArgs)
import System.Exit        ( exitFailure )

import Eazy.Abs   ()
import Eazy.Lex   (Token, mkPosToken)
import Eazy.Par   (pProgram, myLexer)
import Eazy.Print (Print, printTree)
import Eazy.Skel  ()
import TypeChecker (typeCheck)
import Prologue (enrich)
import Interpreter (interpret, eval)

runFile :: FilePath -> IO ()
runFile f = readFile f >>= runProgram

runProgram :: String -> IO ()
runProgram ts = case pProgram $ myLexer ts of
    Left err -> do
      putStrLn $ "Parser Error: " ++ err
      exitFailure
    Right program -> (print . eval . interpret . typeCheck) $ enrich program

showPosToken ((l,c),t) = concat [ show l, ":", show c, "\t", show t ]

showTree :: (Show a, Print a) => a -> IO ()
showTree tree = do
  putStrLn ("\n[Abstract Syntax]\n\n" ++ show tree)
  putStrLn ("\n[Linearized tree]\n\n" ++ printTree tree)

main :: IO ()
main = do
  args <- getArgs
  case args of
    []         -> getContents >>= runProgram
    filename   -> mapM_ runFile filename
