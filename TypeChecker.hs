module TypeChecker (typeCheck) where

import Eazy.ErrM (Err)
import Eazy.Abs
import Control.Monad (foldM, when, unless, void, replicateM)
import Control.Monad.Trans.State (execStateT, get, put, StateT, gets, modify)
import Data.Map.Lazy (empty, Map, member, insert, (!?), (!), adjust)
import Data.List (nub)
import qualified Data.Set as Set
import Control.Applicative ((<|>))

data EazyType =
    EazyInt  |
    EazyBool |
    EazyAny  | -- not correct final type?
    EazyVar String |
    EazyList EazyType |
    EazyCon String [EazyType] |
    EazyFun [EazyType] deriving (Show, Ord)

data PromiseT =
    Fulfilled EazyType Bool |
    Pending Expr EazyType deriving (Show)

instance Eq EazyType where
    EazyInt == EazyInt = True
    EazyBool == EazyBool = True
    EazyAny == _ = True
    _ == EazyAny = True
    EazyVar x == EazyVar y = x == y -- does it really work this way?
    EazyList x == EazyList y = x == y
    EazyCon x y == EazyCon z u = x == z && y == u
    EazyFun x == EazyFun y = x == y
    _ == _ = False

type TypeEnv = (Map String PromiseT, IO())

wget :: Monad m => StateT (s, a) m s
wget = gets fst

wput :: Monad m => s -> StateT (s, a) m ()
wput = modify . (. snd) . (,)

warning :: String -> StateT TypeEnv Err ()
warning msg = do
    (env, io) <- get
    let io' = io >> putStrLn ("Warning: " ++ msg)
    put (env, io')

typeCheck :: Program ->  Err (IO ())
typeCheck (ProgramT _ decls) =
    sndM $ foldM (\e d -> execStateT (translate d) e) (empty, putStr "") decls

translate :: Decl -> StateT TypeEnv Err ()
translate decl  = do
    warning "TypeChecker is not implemented yet"
    case decl of
        DeclFunT pos (VarIdent name) ty -> do
            env <- wget
            when (name `member` env) $
                fail $ posToString pos ++ "Function " ++ name ++ " is already defined"
            pTy@(Fulfilled ty' _) <- translateFunT ty
            checkLast pos ty'
            wput $ insert name pTy env
        DeclData pos (SimpleTypeT _ (ConIdent tname) params) cons -> do
            env <- wget
            when (tname `member` env) $
                fail $ posToString pos ++ "Type " ++ tname ++ " is already defined"
            when (length (nub params) /= length params) $
                fail $ posToString pos ++ "Conflicting parameter names in type " ++ tname
            env <- wget
            wput $ insert tname (Fulfilled (EazyCon tname (devarify <$> params)) True) env
            foldM (`translateDataT` (tname,  params)) () cons
        DeclFunc pos (VarIdent name) args expr -> do
            env <- wget
            unless (name `member` env) $
                fail $ posToString pos ++ "Function " ++ name ++ " type is not defined"
            when (case env !? name of Just (Fulfilled _ True) -> True; _ -> False) $
                fail $ posToString pos ++ "Function " ++ name ++ " has conflictiong definitions"
            when (length (nub args) /= length args) $
                fail $ posToString pos ++ "Conflicting arguments in " ++ name
            let tname = env ! name
            expectedExprType <- getType pos args tname
            wput $ foldr (\(VarIdent a, t) -> insert a (Fulfilled t True)) env (zip args (getTlist tname))
            checkType expectedExprType expr
            wput $ adjust (\(Fulfilled t False) -> Fulfilled t True) name env
    env <- wget
    warning $ show env

getTlist :: PromiseT -> [EazyType]
getTlist (Fulfilled (EazyFun l) _) = l
getTlist (Fulfilled other _) = [other]
getTlist _ = []

checkType :: EazyType -> Expr' BNFC'Position -> StateT TypeEnv Err ()
checkType ty (ExpIf ma ex ex' ex3) = warning "I can't check type of expressions yet"
checkType ty (ExpMth ma ex mas) = warning "I can't check type of expressions yet"
checkType ty (ExpLet ma des ex) = warning "I can't check type of expressions yet"
checkType ty (ExpLmb ma ty' vis ex) = warning "I can't check type of expressions yet"
checkType ty (ExpOr ma ex ex') = warning "I can't check type of expressions yet"
checkType ty (ExpAnd ma ex ex') = warning "I can't check type of expressions yet"
checkType ty (ExpCmp ma ex co ex') = warning "I can't check type of expressions yet"
checkType ty (ExpAdd ma ex ao ex') = warning "I can't check type of expressions yet"
checkType ty (ExpMul ma ex mo ex') = warning "I can't check type of expressions yet"
checkType ty (ExpChn ma ex ex') = warning "I can't check type of expressions yet"
checkType ty (ExpNot ma ex) = warning "I can't check type of expressions yet"
checkType ty (ExpNeg ma ex) = warning "I can't check type of expressions yet"
checkType ty (ExpApp ma ex ex') = warning "I can't check type of expressions yet"
checkType ty (ExpLst ma exs) = warning "I can't check type of expressions yet"
checkType ty (ExpLit ma lit) = warning "I can't check type of expressions yet"
checkType ty (ExpCon ma ci) = warning "I can't check type of expressions yet"
checkType ty (ExpVar ma vi) = warning "I can't check type of expressions yet"


getType :: BNFC'Position -> [VarIdent] -> PromiseT -> StateT TypeEnv Err EazyType
getType pos args promT = do
    case promT of
        Fulfilled (EazyFun l) _ -> do
            x <- foldM (\a e -> e a) l (replicate (length args + 1) (tail' pos))
            return $ EazyFun x
        Fulfilled other _ -> 
            if null args 
                then return other 
                else fail $ posToString pos ++ "Wrong number of arguments"
        _ -> fail $ posToString pos ++ "Unrecognised error"

translateDataT :: () -> (String, [VarIdent]) -> Constr' BNFC'Position -> StateT TypeEnv Err ()
translateDataT _ (tname, args) (ConstrT pos (ConIdent fname) types) = do
    env <- wget
    when (fname `member` env) $
        fail $ posToString pos ++ "Constructor " ++ fname ++ " is already defined"
    types <- mapM translateFunT types
    let fun = EazyFun ((depromise <$> types) ++ [EazyCon tname (devarify <$> args )])
    checkLast pos fun
    wput $ insert fname (Fulfilled fun True) env

depromise :: PromiseT -> EazyType
depromise (Fulfilled ty _) = ty
depromise (Pending _ ty) = ty

devarify :: VarIdent -> EazyType
devarify (VarIdent n) = EazyVar n

translateFunT :: Type' BNFC'Position -> StateT TypeEnv Err PromiseT
translateFunT ty = case ty of
    TypCon _ (ConIdent "Integer") -> return $ Fulfilled EazyInt False
    TypCon _ (ConIdent "Bool")    -> return $ Fulfilled EazyBool False
    TypArr _ ty1 ty2 -> do
        Fulfilled ty1' _ <- translateFunT ty1
        Fulfilled ty2' _ <- translateFunT ty2
        let newTy = case (ty1', ty2') of
                (EazyFun x, EazyFun y) -> EazyFun (x ++ y)
                (EazyFun x, _) -> EazyFun (x ++ [ty2'])
                (_, EazyFun x) -> EazyFun (ty1':x)
                _ -> EazyFun [ty1', ty2']
        return $ Fulfilled newTy False
    TypApp pos (ConIdent name) ty1 tys -> do -- data types
        env <- wget
        case env !? name of
            Just (Fulfilled (EazyCon _ params) _) -> do
                when (1 + length tys /= length params) $
                    fail $ posToString pos ++ "Wrong number of arguments in " ++ name
            _ -> fail $ posToString pos ++ "Type " ++ name ++ " is not defined"
        Fulfilled ty1' _ <- translateFunT ty1
        tys' <- mapM (\x -> do Fulfilled t _ <- translateFunT x; return t) tys
        return $ Fulfilled (EazyCon name $ ty1':tys') False
    TypVar _ (VarIdent name) -> return $ Fulfilled (EazyVar name) False
    TypCon pos (ConIdent name) -> do -- data types
        env <- wget
        case env !? name of
            Just (Fulfilled ty@(EazyCon _ []) _) -> return $ Fulfilled ty False
            _ -> fail $ posToString pos ++ "Type " ++ name ++ " is not defined"
    TypLst _ ty1 -> do
        Fulfilled ty1' _ <- translateFunT ty1
        return $ Fulfilled (EazyList ty1') False

-- Checks if the last element contains only known types ([a] is ok, but Tree a or Int -> b are not)
checkLast :: BNFC'Position -> EazyType -> StateT TypeEnv Err ()
checkLast pos a = void (execStateT (aux a True) Set.empty)
    where
        aux :: EazyType -> Bool -> StateT (Set.Set String) (StateT TypeEnv Err) ()
        aux a err = case a of
            EazyInt -> return ()
            EazyBool -> return ()
            EazyAny -> return ()
            EazyVar s -> do
                when err $ fail $ posToString pos ++ "Unknown type `" ++ s ++ "`"
                env <- get
                put $ Set.insert s env
            EazyList et -> aux et err
            t@(EazyCon _ ets) -> do
                mapM_ (`aux` err) ets
                env <- get
                when (err && not (Set.null env)) $
                    fail $ posToString pos ++ "Unknown type `" ++ show t ++ "`"
            t@(EazyFun ets) -> do
                let ets' = reverse ets
                mapM_ (`aux` False) (tail ets')
                env1 <- get
                aux (head ets) False
                env2 <- get
                when (err && env1 /= env2) $
                    fail $ posToString pos ++ "Unknown type `" ++ show t ++ "`"

-- TODO: move to utils -----------------------------------------------------------------------------
fstM :: Monad m => m (b1, b2) -> m b1
fstM m = do
  (a, _) <- m
  return a

sndM :: Monad m => m (a, b) -> m b
sndM m = do
  (_, b) <- m
  return b

posToString :: BNFC'Position -> String
posToString Nothing = "Position not avaliable: "
posToString (Just (l, c)) = ":" ++ show l ++ ":" ++ show c ++ ": "

tail' :: BNFC'Position -> [EazyType] -> StateT TypeEnv Err [EazyType]
tail' pos [] = fail $ posToString pos ++ "Wrong number of argmuents"
tail' pos (a:as) = return as