module TypeChecker (typeCheck) where

import Eazy.ErrM (Err)
import Eazy.Abs
import Control.Monad (foldM, when, unless)
import Control.Monad.Trans.State (execStateT, get, put, StateT, gets, modify)
import Data.Map.Lazy (empty, Map, member, insert, (!?), (!), adjust, singleton)
import Data.List (nub)
import qualified Data.Set as Set
import Data.Functor ((<&>))

data EazyType =
    EazyInt  |
    EazyBool |
    EazyNil  |
    EazyVar String |
    EazyList EazyType |
    EazyCon String [EazyType] |
    EazyFun [EazyType] deriving (Show, Ord)

type TypeDef = (EazyType, Bool)

type TypeEnv = (Map String TypeDef, IO())

instance Eq EazyType where
    EazyInt == EazyInt = True
    EazyBool == EazyBool = True
    EazyNil == _ = True
    _ == EazyNil = True
    EazyVar x == EazyVar y = x == y
    EazyVar _ == _ = True
    _ ==  EazyVar _ = True
    EazyList x == EazyList y = x == y
    EazyCon x y == EazyCon z u = x == z && y == u
    EazyFun x == EazyFun y = x == y
    _ == _ = False

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
    case decl of
        DeclFunT pos (VarIdent name) ty -> do
            env <- wget
            pTy@(ty', _) <- translateFunT ty
            wput $ insert name pTy env -- Allowing shadowing
        DeclData pos (SimpleTypeT _ (ConIdent tname) params) cons -> do
            env <- wget
            when (tname `member` env) $ -- Not allowing shadowing
                fail $ posToString pos ++ "Type " ++ tname ++ " is already defined"
            when (length (nub params) /= length params) $
                fail $ posToString pos ++ "Conflicting parameter names in type " ++ tname
            wput $ insert tname (EazyCon tname (devarify <$> params), True) env
            foldM (`translateDataT` (tname,  params)) () cons
        DeclFunc pos (VarIdent name) args expr -> do
            env <- wget
            unless (name `member` env) $
                fail $ posToString pos ++ "Function " ++ name ++ " type is not defined"
            -- Allowing shadowing
            when (length (nub args) /= length args) $
                fail $ posToString pos ++ "Conflicting arguments in " ++ name
            let tname = env ! name
            expectedExprType <- forseeExprType pos args tname
            wput $ adjust (\(t, _) -> (t, True)) name (
                foldr (\(VarIdent a, t) -> insert a (t, True)) env (zip args (getTlist tname)))
            exprType <- deduceExprType expr
            when (exprType /= expectedExprType) $
                fail $ posToString pos ++ "Function " ++ name ++ show args ++ " has wrong type" ++
                    "\n\tExpected: " ++ show expectedExprType ++
                    "\n\tActual: " ++ show exprType
            wput $ adjust (\(t, _) -> (t, True)) name env

deduceExprType :: Expr' BNFC'Position -> StateT TypeEnv Err EazyType
deduceExprType (ExpLit _ lit) = return $ case lit of
    LitInt _ v ->  EazyInt
    _ -> EazyBool

deduceExprType (ExpVar pos (VarIdent name)) = do
    env <- wget
    case env !? name of
        Just (t, True) -> return t
        Nothing -> return EazyNil
        _ -> fail $ posToString pos ++ name ++ " is not defined"

deduceExprType (ExpCon pos (ConIdent name)) = do
    env <- wget
    case env !? name of
        Just (EazyFun lst, True) -> case lst of
            [t] -> return t
            [] -> fail $ posToString pos ++ "Unexpected error - 1"
            _ -> return $ EazyFun lst
        _ -> fail $ posToString pos ++ name ++ " is not defined"

deduceExprType (ExpIf pos texpr bexpr fexpr) = do
    bexprType <- deduceExprType bexpr
    when (bexprType /= EazyBool) $
        fail $ posToString pos ++ "Expected boolean expression, got " ++ show bexprType
    fexprType <- deduceExprType fexpr
    texprType <- deduceExprType texpr
    when (texprType /= fexprType) $
        fail $ posToString pos ++ "If branches have different types. Got " ++
            show texprType ++ " and " ++ show fexprType
    return texprType

deduceExprType (ExpOr pos expr expr') = deduceOpTypes EazyBool pos [expr, expr']

deduceExprType (ExpAnd pos expr expr') = deduceOpTypes EazyBool pos [expr, expr']

deduceExprType (ExpCmp pos expr cop expr') = do
    exprType <- deduceExprType expr
    when (exprType /= EazyInt) $
        fail $ posToString pos ++ "Expected integer expression, got " ++ show exprType
    exprType' <- deduceExprType expr'
    when (exprType' /= EazyInt) $
        fail $ posToString pos ++ "Expected integer expression, got " ++ show exprType'
    return EazyBool

deduceExprType (ExpAdd pos expr _ expr') = deduceOpTypes EazyInt pos [expr, expr']

deduceExprType (ExpMul pos expr _ expr') = deduceOpTypes EazyInt pos [expr, expr']

deduceExprType (ExpNot pos expr) = deduceOpTypes EazyBool pos [expr]

deduceExprType (ExpNeg pos expr) = deduceOpTypes EazyInt pos [expr]

deduceExprType (ExpChn pos expr expr') = do
    exprType <- deduceExprType expr
    expr'Type <- deduceExprType expr'
    when (expr'Type /= EazyList exprType) $
        fail $ posToString pos ++ "Expected list of " ++ show exprType ++ ", got " ++ show expr'Type
    return $ EazyList exprType

deduceExprType (ExpLst pos exprs) = case exprs of
    [] -> return $ EazyList EazyNil
    [expr] -> do
        exprType <- deduceExprType expr
        return $ EazyList exprType
    h:t -> do
        hType <- deduceExprType h
        deduceOpTypes hType pos t
        return $ EazyList hType

deduceExprType (ExpLet _ decls expr) = do
    env <- wget
    mapM_ translate decls
    exprType <- deduceExprType expr
    wput env
    return exprType

deduceExprType (ExpLmb pos ty vis expr) = do
    pt@(lambdaType, _) <- translateFunT ty
    expectedExprType <- forseeExprType pos vis pt
    exprType <- deduceExprType expr
    when (exprType /= expectedExprType) $
        fail $ posToString pos ++ "Lambda has conflicting type. Got " ++
            show exprType ++ " and " ++ show expectedExprType
    return lambdaType

deduceExprType (ExpApp pos expr expr') = do
    exprType <- deduceExprType expr
    case exprType of
        EazyFun lst -> do
            expr'Type <- deduceExprType expr'
            case lst of
                [a, b] -> do
                    if a == expr'Type
                    then return b
                    else case a of
                        EazyVar name -> return  $ subtypeWith (singleton name expr'Type) b
                        _ -> fail $ posToString pos ++ "Wrong type of argument. Expected " ++
                            show expr'Type ++ ", got " ++ show a
                a:t -> if a == expr'Type
                    then return $ EazyFun t
                    else case a of
                        EazyVar name -> return $ subtypeWith (singleton name expr'Type) $ EazyFun t
                        _ -> fail $ posToString pos ++ "Wrong type of argument. Expected " ++
                            show expr'Type ++ ", got " ++ show a
                _  -> fail $ posToString pos ++ "Unexpected error - 2"
        _ -> fail $ posToString pos ++ "Expected function, got " ++ show exprType

deduceExprType (ExpMth _ expr matchings) = do
    exprType <- deduceExprType expr
    mapM_ (\(MatchT p pat _) -> do
        patType <- deducePatternType pat
        when (patType /= exprType) $
            fail $ posToString p ++ "Error in pattern type. Expected " ++
                show exprType ++ ", got " ++ show patType
        ) matchings
    foldM (\t (MatchT p apat e) -> do
        env <- wget
        case apat of
            PatAs _ pat (VarIdent v) -> do
                wput $ insert v (exprType, True) env
                enrichEnvWithPat pat exprType
            Pat _ pat -> enrichEnvWithPat pat exprType
        resExprType <- deduceExprType e
        wput env
        if t == EazyNil
            then return resExprType
            else fail $ posToString p ++ "Conflicting types. Expected " ++
                show t ++ ", got " ++ show resExprType
        ) EazyNil matchings

subtypeWith :: Map String EazyType -> EazyType -> EazyType
subtypeWith repl (EazyVar s) = case repl !? s of {Nothing -> EazyVar s; Just t -> t}
subtypeWith repl (EazyList nt) = EazyList $ subtypeWith repl nt
subtypeWith repl (EazyCon s nts) = EazyCon s $ map (subtypeWith repl) nts
subtypeWith repl (EazyFun nts) = EazyFun $ map (subtypeWith repl) nts
subtypeWith _ res = res

enrichEnvWithPat :: Pattern' BNFC'Position -> EazyType -> StateT TypeEnv Err ()
enrichEnvWithPat (PatCon _ (ConIdent name) sps) (EazyCon con ts) = do
    env <- wget
    let (EazyFun args', _) = env ! name
    let (EazyCon _ names', _) = env ! con
    let names = map (\(EazyVar v) -> v) names'
    let m = foldl (\m (n, t) -> insert n t m) empty (zip names ts)
    let args = map (subtypeWith m) args'
    mapM_ (\(t, SubPatT _ p) -> enrichEnvWithPat p t) (zip args sps)
enrichEnvWithPat (PatLL _ pat pat') (EazyList t) =
    enrichEnvWithPat pat t >> enrichEnvWithPat pat' (EazyList t)
enrichEnvWithPat (PatLst _ pats) (EazyList t) = mapM_ (`enrichEnvWithPat` t) pats
enrichEnvWithPat (PatLit _ _) t = return ()
enrichEnvWithPat (PatVar _ (VarIdent  v)) t = do
    env <- wget
    wput $ insert v (t, True) env
enrichEnvWithPat (PatDef _) t = return ()
enrichEnvWithPat p t = fail $ "Unexpected pattern: " ++ show p ++ " with type " ++ show t

deducePatternType :: AbsPattern' BNFC'Position -> StateT TypeEnv Err EazyType
deducePatternType pat =
    let aux :: Pattern' BNFC'Position -> StateT TypeEnv Err EazyType
        aux (PatCon pos (ConIdent name) sps) = do
            env <- wget
            case env !? name of
                Just (EazyFun lst, _) -> do
                    when (length sps + 1 /= length lst) $
                        fail $ posToString pos ++ "Wrong number of arguments."
                    types <- mapM (\(SubPatT _ pat, et) -> do
                        patType <- aux pat
                        return et
                        ) (zip sps lst)
                    fstM $ foldM (subtypeConPat pos) (head lst, empty) (zip types (tail lst))
                _ -> fail $ posToString pos ++ name ++ " is not defined"
        aux (PatLL pos pat1 pat2) = do
            pat1Type <- aux pat1
            pat2Type <- aux pat2
            when (EazyList pat1Type /= pat2Type) $ conflictError pos pat1Type pat2Type
            return pat2Type
        aux (PatLst pos pats) = case pats of
            [] -> return $ EazyList EazyNil
            [p] -> aux p <&> EazyList
            h:t -> do
                expPatType <- aux h
                mapM_ (\e -> do
                    patType <- aux e
                    when (patType /= expPatType) $ conflictError pos expPatType patType
                    ) t
                return $ EazyList expPatType
        aux (PatLit _ lit) = return $ case lit of {LitInt _ _ -> EazyInt; _ -> EazyBool}
        aux (PatVar _ _) = return EazyNil
        aux (PatDef _) = return EazyNil
    in case pat of
        PatAs _ pat' _ -> aux pat'
        Pat _ pat' -> aux pat'

subtypeConPat :: BNFC'Position -> (EazyType, Map String EazyType) -> (EazyType, EazyType) ->
            StateT TypeEnv Err (EazyType, Map String EazyType)
subtypeConPat pos (arg, m) (t, next) = case t of
    EazyInt -> case arg of
        EazyVar s -> let m = insert s t m in
            return (subtypeWith m next, m)
        EazyInt -> return (subtypeWith m next, m)
        _ -> conflictError pos arg t
    EazyBool -> case arg of
        EazyVar s -> let m = insert s t m in
            return (subtypeWith m next, m)
        EazyBool -> return (subtypeWith m next, m)
        _ -> conflictError pos arg t
    EazyNil -> return (subtypeWith m next, m)
    EazyVar s -> return (subtypeWith m next, m)
    EazyList t' -> case arg of
        EazyVar s -> let m = insert s t m in
            return (subtypeWith m next, m)
        EazyList nt -> subtypeConPat pos (nt, m) (t', next)
        _ -> conflictError pos arg t
    EazyCon s t's -> case arg of
        EazyVar s -> let m = insert s t m in
            return (subtypeWith m next, m)
        EazyCon s' ets -> if s' == s
            then foldM (subtypeConPat pos) (head ets, m) (zip t's (tail ets ++ [next]))
            else conflictError pos arg t
        _ -> conflictError pos arg t
    EazyFun t's -> case arg of
        EazyVar s -> let m = insert s t m in
            return (subtypeWith m next, m)
        EazyFun ets -> foldM (subtypeConPat pos) (head ets, m) (zip t's (tail ets ++ [next]))
        _ -> conflictError pos arg t

conflictError :: MonadFail m => BNFC'Position -> EazyType -> EazyType -> m a
conflictError pos arg1 arg2 = fail $ posToString pos ++ "Conflicting pattern types. Got " ++
    show arg1 ++ " and " ++ show arg2

deduceOpTypes :: EazyType -> BNFC'Position -> [Expr' BNFC'Position] -> StateT TypeEnv Err EazyType
deduceOpTypes exType pos exprs = do
    mapM_ (\e -> do
        t <- deduceExprType e
        when (t /= exType) $
            fail $ posToString pos ++ "Expected boolean expression, got " ++ show t
        ) exprs
    return exType

forseeExprType :: BNFC'Position -> [VarIdent] -> TypeDef -> StateT TypeEnv Err EazyType
forseeExprType pos args promT = do
    case promT of
        (EazyFun l, _) -> do
            x <- foldM (\a e -> e a) l (replicate (length args) (tail' pos))
            case x of
                [a] -> return a
                [] -> fail $ posToString pos ++ "Unexpected error - 4"
                _ -> return $ EazyFun x
        (other, _) ->
            if null args
                then return other
                else fail $ posToString pos ++ "Wrong number of arguments"

translateDataT :: () -> (String, [VarIdent]) -> Constr' BNFC'Position -> StateT TypeEnv Err ()
translateDataT _ (tname, args) (ConstrT pos (ConIdent fname) types) = do
    env <- wget
    when (fname `member` env) $
        fail $ posToString pos ++ "Constructor " ++ fname ++ " is already defined"
    types <- mapM translateFunT types

    let varSet = Set.fromList $ map (\(VarIdent n) -> n) args
    mapM_ (\(a, _) -> errorIfNewVars pos varSet a) types

    let fun = EazyFun ((fst <$> types) ++ [EazyCon tname (devarify <$> args )])
    wput $ insert fname (fun, True) env

errorIfNewVars :: BNFC'Position -> Set.Set String -> EazyType -> StateT TypeEnv Err ()
errorIfNewVars pos set t = case t of
    EazyVar str -> unless (str `Set.member` set) $
        fail $ posToString pos ++ "Unrecognised variable " ++ str
    EazyList nt -> errorIfNewVars pos set nt
    EazyCon _ nts -> mapM_ (errorIfNewVars pos set) nts
    EazyFun nts -> mapM_ (errorIfNewVars pos set) nts
    _ -> return ()

devarify :: VarIdent -> EazyType
devarify (VarIdent n) = EazyVar n

translateFunT :: Type' BNFC'Position -> StateT TypeEnv Err TypeDef
translateFunT ty = case ty of
    TypCon _ (ConIdent "Integer") -> return (EazyInt, False)
    TypCon _ (ConIdent "Bool")    -> return (EazyBool, False)
    TypArr _ ty1 ty2 -> do
        (ty1', _) <- translateFunT ty1
        (ty2', _) <- translateFunT ty2
        let newTy = case ty2' of
                EazyFun x -> EazyFun (ty1':x)
                _ -> EazyFun [ty1', ty2']
        return (newTy, False)
    TypApp pos (ConIdent name) ty1 tys -> do -- data types
        env <- wget
        case env !? name of
            Just (EazyCon _ params, _) -> do
                when (1 + length tys /= length params) $
                    fail $ posToString pos ++ "Wrong number of arguments in " ++ name
            _ -> fail $ posToString pos ++ "Type " ++ name ++ " is not defined"
        (ty1', _) <- translateFunT ty1
        tys' <- mapM (\x -> do (t, _ ) <- translateFunT x; return t) tys
        return (EazyCon name $ ty1':tys', False)
    TypVar _ (VarIdent name) -> return (EazyVar name, False)
    TypCon pos (ConIdent name) -> do -- data types
        env <- wget
        case env !? name of
            Just (ty@(EazyCon _ []), _) -> return (ty, False)
            _ -> fail $ posToString pos ++ "Type " ++ name ++ " is not defined"
    TypLst _ ty1 -> do
        (ty1', _) <- translateFunT ty1
        return (EazyList ty1', False)

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

getTlist :: TypeDef -> [EazyType]
getTlist (EazyFun l, _) = l
getTlist (other, _) = [other]
