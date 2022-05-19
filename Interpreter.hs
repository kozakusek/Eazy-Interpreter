module Interpreter (interpret, evalMain) where

import Eazy.ErrM (Err)
import Eazy.Abs
import Control.Monad.Trans.State (execStateT, StateT, get, put, modify)
import Data.Map.Lazy (empty, Map, insert, (!?))
import Control.Monad (foldM)
import Control.Monad.Trans.Reader (runReaderT, ReaderT, reader, local, ask)
import Data.Functor ((<&>))
import Data.List (find)

type Env = Map String Promise

data EazyValue =
    IntVal Integer |
    BoolVal Bool |
    ListVal [EazyValue] |
    AlgVal ConIdent [EazyValue] |
    FunVal [VarIdent] Promise deriving (Eq)

instance Show EazyValue where
    show (IntVal n) = show n
    show (BoolVal b) = show b
    show (ListVal evs) = "[" ++
        fst (foldr (\ev (s, b) -> (show ev ++ (if b then "," else "") ++ s, True)) ("]", False) evs)
    show (AlgVal (ConIdent n) []) = n
    show (AlgVal (ConIdent n) evs) = n ++ "(" ++
        fst (foldr (\ev (s, b) -> (show ev ++ (if b then "," else "") ++ s, True)) (")", False) evs)
    show (FunVal _ _) = "Unfortunately, I can't show functions :("

data Promise =
    Fulfilled EazyValue |
    Pending Expr Env |
    PendingAlg ConIdent Integer [EazyValue] Env deriving (Eq)

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
        _ -> fail $ posToString pos ++ "Variable " ++ var ++ " is not defined"

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

evalExpr (ExpEqs ma ex co ex') = do
    n <- evalExpr ex
    n' <- evalExpr ex'
    return $ BoolVal $ f co n n' -- TODO: check if for all otptions it works
    where
        f (OpEq _)  = (==)
        f (OpNeq _) = (/=)

evalExpr (ExpCmp ma ex co ex') = do
    IntVal n <- evalExpr ex
    IntVal n' <- evalExpr ex'
    return $ BoolVal $ f co n n'
    where
        f (OpLrt _) = (<)
        f (OpGrt _) = (>)
        f (OpLeq _) = (<=)
        f (OpGeq _) = (>=)

evalExpr (ExpIf _ ex1 ex' ex2) = do
    BoolVal condition <- evalExpr ex'
    if condition then evalExpr ex1 else evalExpr ex2

evalExpr (ExpApp pos f g) = do
    pending <- evalExpr f
    case pending of
        FunVal args (Pending expr env') -> do
            env <- ask
            case args of
                [VarIdent a] -> local (\v -> insert a (Pending g v) env') (evalExpr expr)
                (VarIdent a):as -> return $ FunVal as $ Pending expr $ insert a (Pending g env) env'
                _ -> undefined
        FunVal args (PendingAlg (ConIdent name) n vals env') -> do
            v <- evalExpr g
            case n of
                1 -> return $ AlgVal (ConIdent name) (vals ++ [v])
                _ -> return $ FunVal args $ PendingAlg (ConIdent name) (n - 1) (vals ++ [v]) env'
        _ -> fail $ posToString pos ++ "Not a function"

evalExpr (ExpChn _ ex ex') = do
    h <- evalExpr ex
    ListVal l <- evalExpr ex'
    return $ ListVal $ h : l

evalExpr (ExpLst _ exs)  = mapM evalExpr exs <&> ListVal

evalExpr (ExpLmb _ vis ex) = FunVal vis . Pending ex <$> ask

evalExpr (ExpLet ma decls ex) = do
    env <- ask
    let (Right env') = foldM (\e d -> execStateT (translate d) e) env decls
    local (const env') (evalExpr ex)

evalExpr (ExpCon pos c@(ConIdent name)) = do
    env <- ask
    case env !? name of
        Just alg@(PendingAlg _ n _ _) -> return $ if n == 0 then AlgVal c [] else FunVal [] alg
        _ -> fail $ posToString pos ++ "Constructor " ++ name ++ " is not defined"

evalExpr (ExpMth ma ex mas) = do
    seq <- evalExpr ex
    case find (\(MatchT _ pat expr) -> seq `matches` pat) mas of
        Just (MatchT _ pat expr) -> local (letify seq pat) (evalExpr expr)
        _ -> fail $ posToString ma ++ "No matching method found for " ++ show seq

letify :: EazyValue -> AbsPattern' BNFC'Position -> Env -> Env
letify v p env = case (v, p') of
    (_, PatDef _) -> env'
    (_, PatLit _ lit) -> env'
    (v, PatVar _ (VarIdent name)) -> insert name (Fulfilled v) env'
    (ListVal (h:t), PatLL _ pat pat') ->
        letify (ListVal t) (Pat Nothing pat') $ letify h (Pat Nothing pat) env'
    (ListVal vs, PatLst _ pats) -> foldr (\(v, p) -> letify v $ Pat Nothing p) env' $ zip vs pats
    (AlgVal name vs, PatCon _ _ sps) ->
        foldr (\(v, SubPatT _ pat) -> letify v (Pat Nothing pat)) env' $ zip vs sps
    _ -> env'
    where
        (env', p') = case p of
            PatAs _ pat (VarIdent name) -> (insert name (Fulfilled v) env, pat)
            Pat _ pat -> (env, pat)

matches :: EazyValue -> AbsPattern' BNFC'Position -> Bool
matches v p = case p of
    PatAs _ pat _ -> fst $ v `isLike` (pat, empty)
    Pat _ pat -> fst $ v `isLike` (pat, empty)
    where
        isLike :: EazyValue -> (Pattern' BNFC'Position, Env) -> (Bool, Env)
        isLike v (pat, env) = case (v, pat) of
            (_, PatDef _) -> (True, env)
            (_, PatLit _ lit) -> (case (lit, v) of
                (LitInt _ n, IntVal n') -> n == n'
                (LitTrue _, BoolVal True) -> True
                (LitFalse _, BoolVal False) -> True
                _ -> False, env)
            (_, PatVar _ (VarIdent name)) -> case env !? name of
                Just (Fulfilled v') -> (v == v', env)
                _ -> (True, insert name (Fulfilled v) env)
            (ListVal (h:t), PatLL _ patH patT) -> case h `isLike` (patH, env) of
                (True, env') -> ListVal t `isLike` (patT, env')    where
                _ -> (False, env)
            (ListVal vs, PatLst _ ps) -> if length vs == length ps then
                foldr (\(a, p) r@(b, e) -> if b then a `isLike` (p, e) else r)
                    (True, env) (zip vs ps)
                else (False, env)
            (AlgVal name vs, PatCon _ name' sps) -> if name == name' && length vs == length sps then
                foldr (\(a, SubPatT _ p) r@(b, e) -> if b then a `isLike` (p, e) else r)
                    (True, env) (zip vs sps)
                else (False, env)
            _ -> (False, env)

evalMain :: Env -> Err EazyValue
evalMain a = case a !? "main" of
    Just (Fulfilled val) -> return val
    Just (Pending expr env) -> evalExprInEnv expr env
    _ -> return $ IntVal (-1)

interpret :: Program -> Err Env
interpret (ProgramT _ decls) = foldM (\env decl -> execStateT (translate decl) env) empty decls

translate :: Decl -> StateT Env Err ()
translate d = case d of
    DeclData _ (SimpleTypeT _ _ args) cons -> do
        env <- get
        let env' = foldr (\(ConstrT _ n@(ConIdent name) lst) a ->
                insert name (PendingAlg n (toInteger $ length lst) [] env') a) env cons
        put env'
    DeclFunc _ (VarIdent name) vis expr -> do
        env <- get
        let env' = insert name (
                if null vis then Pending expr env'
                else Fulfilled $ FunVal vis $ Pending expr env'
                ) env
        put env'
    DeclFunT _ vi ty -> modify id
