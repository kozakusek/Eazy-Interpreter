module Interpreter (interpret, evalMain ) where

import Eazy.ErrM ( Err )
import Eazy.Abs (Program, Program' (ProgramT), Decl, ConIdent, Expr)
import Control.Monad.Trans.State (execStateT, StateT)
import Data.Map.Lazy (empty, Map)

type Env = Map String Bool -- MyType

evalMain :: Env -> Err String
evalMain = undefined

interpret :: Program -> Err Env
interpret (ProgramT _ decls) = execStateT (translate $ head decls) empty

translate :: Decl -> StateT Env Err ()
translate = undefined 
