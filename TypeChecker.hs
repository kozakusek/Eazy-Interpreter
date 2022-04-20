module TypeChecker (typeCheck) where

import Eazy.ErrM (Err)
import Eazy.Abs
import Control.Monad (foldM, when, unless, liftM2)
import Control.Monad.Trans.State (execStateT, get, put, StateT, gets, modify)
import Data.Map.Lazy (empty, Map, member, insert, (!?), (!))
import Data.List (nub)

data EazyType =
    EazyInt  |
    EazyBool |
    EazyAny  |
    EazyVar String |
    EazyList EazyType |
    EazyApp EazyType EazyType |
    EazyFun EazyType EazyType deriving (Show, Ord)

data PromiseT =
    Fulfilled EazyType Bool |
    Pending Expr EazyType

instance Eq EazyType where
    EazyInt == EazyInt = True
    EazyBool == EazyBool = True
    EazyAny == _ = True
    _ == EazyAny = True
    EazyVar x == EazyVar y = x == y
    EazyList x == EazyList y = x == y
    EazyApp x y == EazyApp z w = x == z && y == w
    EazyFun x y == EazyFun z w = x == z && y == w
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
    sndM $ foldM (\env decl -> execStateT (translate decl) env) (empty, putStr "") decls

translate :: Decl -> StateT TypeEnv Err ()
translate decl  = do
    warning "TypeChecker is not implemented yet"
    case decl of
        DeclFunT pos (VarIdent name) ty -> do
            env <- wget
            when (name `member` env) $
                fail $ posToString pos ++ "Function " ++ name ++ " is already defined"
            ty' <- translateFunT ty
            wput $ insert name ty' env
        DeclData pos (SimpleTypeT _ (ConIdent tname) params) cons -> do
            env <- wget
            when (tname `member` env) $
                fail $ posToString pos ++ "Type " ++ tname ++ " is already defined"
            when (length (nub params) /= length params) $
                fail $ posToString pos ++ "Conflicting parameter names in type " ++ tname
            foldM (`translateDataT` params) () cons
        DeclFunc pos (VarIdent name) args expr -> do
            env <- wget
            unless (name `member` env) $
                fail $ posToString pos ++ "Function " ++ name ++ " type is not defined"
            when (case env !? name of Just (Fulfilled _ True) -> True; _ -> False) $
                fail $ posToString pos ++ "Function " ++ name ++ " has conflictiong definitions"
            when (length (nub args) /= length args) $
                fail $ posToString pos ++ "Conflicting arguments in " ++ name
            expectedExprType <- getType args $ env ! name
            checkType expectedExprType expr

checkType :: EazyType -> Expr' BNFC'Position -> StateT TypeEnv Err ()
checkType ty expr = warning "I can't check type of expressions yet"

getType :: [VarIdent] -> PromiseT -> StateT TypeEnv Err EazyType
getType args promT = do
    warning "I can't get type of args yet"
    return EazyAny

translateDataT :: () -> [VarIdent] -> Constr' BNFC'Position -> StateT TypeEnv Err ()
translateDataT _ a b = do
    warning "Creating data types is not implemented yet"
    return ()

translateFunT :: Type' BNFC'Position -> StateT TypeEnv Err PromiseT
translateFunT a = do
    warning "Creating function type is not implemented yet"
    return $ Fulfilled EazyAny False


-- TODO: move to utils -----------------------------------------------------------------------------
fstM :: Monad m => m (b1, b2) -> m b1
fstM m = do
  (a, _) <- m
  return a

sndM :: Monad m => m (a, b) -> m b
sndM m = do
  (_, b) <- m
  return b

posToString :: Maybe (Int, Int) -> String
posToString Nothing = "Position not avaliable: "
posToString (Just (l, c)) = ":" ++ show l ++ ":" ++ show c ++ ": "