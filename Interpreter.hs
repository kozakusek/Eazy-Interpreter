module Interpreter (interpret, evalMain ) where

import Eazy.ErrM ( Err )
import Eazy.Abs
import Control.Monad.Trans.State (execStateT, StateT, get, put, modify)
import Data.Map.Lazy (empty, Map, insert, (!?) )
import Control.Monad ( foldM )
import Control.Monad.Trans.Reader (runReaderT, ReaderT, reader, local, ask)
import Prelude hiding (lookup)
import Data.Functor ((<&>))

type Env = Map String Promise

data EazyValue =
    IntVal Integer |
    BoolVal Bool |
    ListVal [EazyValue] |
    AlgVal ConIdent [EazyValue] |
    FunVal [VarIdent] Promise deriving (Eq, Show) -- Ugly, but it works

data Promise =
    Fulfilled EazyValue |
    Pending Expr Env deriving (Eq, Show)

posToString :: Maybe (Int, Int) -> String
posToString Nothing = "Position not avaliable: "
posToString (Just (l, c)) = ":" ++ show l ++ ":" ++ show c ++ ": "

evalExprInEnv :: Expr -> Env -> Err EazyValue
evalExprInEnv = runReaderT . evalExpr

evalExpr :: Expr -> ReaderT Env Err EazyValue
evalExpr (ExpLit pos lit) = case lit of
  LitInt _ n -> return $ IntVal n
  LitTrue _  -> return $ BoolVal True
  LitFalse _ -> return $ BoolVal False

evalExpr (ExpVar pos (VarIdent var)) = do
    env <- ask
    case env !? var  of
        Just (Fulfilled v) -> return v
        Just (Pending e env') -> local (const env') (evalExpr e)
        Nothing -> fail $ posToString pos ++ "Variable " ++ var ++ " is not defined"

evalExpr (ExpNeg _ ex) = evalExpr ex >>= (\(IntVal n) -> return $ IntVal $ -n)

evalExpr (ExpAdd _ ex op ex') = do
    IntVal n' <- evalExpr ex'
    IntVal n <- evalExpr ex
    return $ IntVal $ f op n n'
    where
        f (OpAdd _) = (+)
        f (OpSub _) = (-)

evalExpr (ExpMul _ ex op ex') = do
    IntVal n' <- evalExpr ex'
    case (op, n') of
        (OpDiv pos, 0) -> fail $ posToString pos ++ "Division by zero"
        (OpDiv _, _) -> evalExpr ex >>= (\(IntVal n) -> return $ IntVal $ n `div` n')
        (OpMul _, _) -> evalExpr ex >>= (\(IntVal n) -> return $ IntVal $ n * n')

evalExpr (ExpNot _ ex) = evalExpr ex >>= (\(BoolVal b) -> return $ BoolVal $ not b)

evalExpr (ExpOr _ ex ex') = do
    BoolVal b <- evalExpr ex
    BoolVal b' <- evalExpr ex'
    return $ BoolVal $ b || b'

evalExpr (ExpAnd ma ex ex') = do
    BoolVal b <- evalExpr ex
    BoolVal b' <- evalExpr ex'
    return $ BoolVal $ b && b'

evalExpr (ExpCmp ma ex co ex') = do
    IntVal n <- evalExpr ex
    IntVal n' <- evalExpr ex'
    return $ BoolVal $ f co n n'
    where
        f (OpEq _)  = (==)
        f (OpNeq _) = (/=)
        f (OpLrt _) = (<)
        f (OpGrt _) = (>)
        f (OpLeq _) = (<=)
        f (OpGeq _) = (>=)

evalExpr (ExpIf _ ex1 ex' ex2) = do
    BoolVal condition <- evalExpr ex'
    if condition then evalExpr ex1 else evalExpr ex2

evalExpr (ExpApp pos f g) = do
    FunVal args (Pending expr env') <- evalExpr f
    env <- ask
    case args of
      [VarIdent a] -> local (\v -> insert a (Pending g v) env') (evalExpr expr)
      (VarIdent a):as -> return $ FunVal as $ Pending expr $ insert a (Pending g env) env'
      _ -> undefined

evalExpr (ExpChn _ ex ex') = do
    h <- evalExpr ex
    ListVal l <- evalExpr ex'
    return $ ListVal $ h : l

evalExpr (ExpLst _ exs)  = mapM evalExpr exs <&> ListVal

evalExpr (ExpLmb _ _ vis ex) = FunVal vis . Pending ex <$> ask

evalExpr (ExpLet ma decls ex) = do
    env <- ask
    let (Right env') = foldM (\e d -> execStateT (translate d) e) env decls
    local (const env') (evalExpr ex)

evalExpr (ExpCon ma (ConIdent name)) = undefined

evalExpr (ExpMth ma ex mas) = undefined

evalMain :: Env -> Err EazyValue
evalMain a = case a !? "main" of
    Just (Fulfilled val) -> return val
    Just (Pending expr env) -> evalExprInEnv expr env
    Nothing -> return $ IntVal 0

interpret :: Program -> Err Env
interpret (ProgramT _ decls) = foldM (\env decl -> execStateT (translate decl) env) empty decls

translate :: Decl -> StateT Env Err ()
translate d = case d of
    DeclData _ (SimpleTypeT _ _ args) cons -> modify id
    DeclFunc _ (VarIdent name) vis expr -> do
        env <- get
        let env' = insert name (
                if null vis then Pending expr env'
                else Fulfilled $ FunVal vis $ Pending expr env'
                ) env
        put env'
    DeclFunT _ vi ty -> modify id
