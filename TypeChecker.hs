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
    EazyVar String |
    EazyList EazyType |
    EazyCon String [EazyType] |
    EazyFun [EazyType] deriving (Show)

type TypeDef = (EazyType, Bool)

instance Eq EazyType where -- TODO: fucking bullshit!!!!, fun, con, var???
    EazyInt == EazyInt = True
    EazyBool == EazyBool = True
    EazyVar x == EazyVar y = x == y
    EazyList x == EazyList y = x == y
    EazyCon x y == EazyCon z u = x == z && y == u
    EazyFun x == EazyFun y = x == y
    _ == _ = False

tStream :: [String]
tStream = let aux n = show n : aux (n + 1) in aux 0

type TypeEnv = (Map String TypeDef, (IO(), ([String], String -> Maybe EazyType)))

type EnvM a = StateT TypeEnv Err a -- TODO cleanup by using it

emptyEnv :: TypeEnv
emptyEnv = (empty, (putStr "", (tStream, const Nothing)))

getE :: Monad m => StateT (s, a) m s
getE = gets fst

putE :: Monad m => s -> StateT (s, a) m ()
putE = modify . (. snd) . (,)

warning :: String -> StateT TypeEnv Err ()
warning msg = do
    (env, (io, types)) <- get
    let io' = io >> putStrLn ("Warning: " ++ msg)
    put (env, (io', types))

getT :: Monad m => StateT (s, (a, ([b], c))) m b
getT = do
    (env, (io, (ts, m))) <- get
    put (env, (io, (tail ts, m)))
    return $ head ts

getNT :: Monad m => Int -> StateT (s, (a, ([b], c))) m [b]
getNT n = do
    (env, (io, (ts, m))) <- get
    put (env, (io, (foldl (flip id) ts (replicate n tail), m)))
    return $ take n ts

resetT :: Monad m => StateT (s, (a, ([String], c -> Maybe d))) m () -- Resets typeStream and mapping
resetT = do
    (env, (io, _)) <- get
    put (env, (io, (tStream, const Nothing)))

updateM :: Monad m => String -> EazyType -> StateT (s, (a, (b, String -> Maybe EazyType))) m ()
updateM x t = do
    (env, (io, (str, mapping))) <- get
    let mapping' a = if a == x then Just t
        else case mapping a of
            Just (EazyVar a') -> if a' == x then Just t else Just (EazyVar a')
            a' -> a'
    put (env, (io, (str, mapping')))

getM :: Monad m => t0 -> StateT (s, (a, (b, t0 -> Maybe EazyType))) m (Maybe EazyType)
getM x = do
    (env, (io, (str, mapping))) <- get
    put (env, (io, (str, mapping)))
    return $ mapping x

typeCheck :: Program ->  Err (IO ())
typeCheck (ProgramT _ decls) =
    fstM $ sndM $ foldM (\e d -> execStateT (translate True d) e) emptyEnv decls

translate :: Bool -> Decl -> StateT TypeEnv Err ()
translate isTop decl = do -- TODO: cleanup by removing case decl of
    case decl of
        DeclFunT pos (VarIdent name) ty -> do
            env <- getE
            pTy@(ty', defined) <- translateFunT ty
            when (name `member` env) $ if defined
                then
                    unless (fst (env ! name) == ty') $ fail $ posToString pos ++
                        "Function " ++ name ++ " already defined with different type"
                else
                    fail $ posToString pos ++ "Function " ++ name ++ " is already declared"
            putE $ insert name pTy env
        DeclData pos (SimpleTypeT _ (ConIdent tname) params) cons -> do
            env <- getE
            when (tname `member` env) $
                fail $ posToString pos ++ "Type " ++ tname ++ " is already defined"
            when (length (nub params) /= length params) $
                fail $ posToString pos ++ "Conflicting parameter names in type " ++ tname
            putE $ insert tname (EazyCon tname (devarify <$> params), True) env
            foldM (`translateDataT` (tname,  params)) () cons
        DeclFunc pos (VarIdent name) args expr -> do
            env <- getE
            when (length (nub args) /= length args) $
                fail $ posToString pos ++ "Conflicting arguments in " ++ name
            ts' <- getNT (1 + length args)
            let ts = EazyVar <$> ts'
            putE $ adjust (const (EazyFun ts, True)) name (
               foldr (\(VarIdent a, t) -> insert a (t, True)) env (zip args ts))
            exprType <- deduceExprType expr
            -- extract mappings for ts
            updateM (last ts') exprType
            funType <- mapExpr (EazyFun ts)
            -- if defined and not equal then error else add type to env
            case env !? name of
                Nothing -> return ()
                Just (et, False) -> if et == funType then return ()
                    else fail $ posToString pos ++ "Type mismatch in " ++ name ++ ": " ++ show et ++ " != " ++ show funType
                Just (et, True) -> fail $ posToString pos ++ "Function " ++ name ++ " is already defined"

            -- if top_translate then reset Types and mappings else do nothing
            unless isTop resetT

            putE $ adjust (const (funType, True)) name env

mapExpr :: EazyType -> StateT TypeEnv Err EazyType
mapExpr et = case et of
    EazyVar v -> do
        t <- getM v
        case t of {Just t' -> return t'; Nothing -> return $ EazyVar v}
    EazyList et -> mapExpr et <&> EazyList
    EazyCon s ets -> mapM mapExpr ets <&> EazyCon s
    EazyFun ets -> mapM mapExpr ets <&> EazyFun
    t -> return t

deduceExprType :: Expr' BNFC'Position -> StateT TypeEnv Err EazyType
deduceExprType (ExpLit _ lit) = return $ case lit of -- OK
    LitInt _ v ->  EazyInt
    _ -> EazyBool

deduceExprType (ExpVar pos (VarIdent name)) = do -- OK
    env <- getE
    case env !? name of
        Just (t, True) -> return t
        _ -> fail $ posToString pos ++ "\"" ++ name ++ "\" is not defined"

deduceExprType (ExpCon pos (ConIdent name)) = do -- OK
    env <- getE
    case env !? name of
        Just (EazyFun lst, True) -> case lst of
            [t] -> return t
            [] -> fail $
                posToString pos ++ "Unexpected error - Constructor " ++ name ++ " has no type"
            _ -> return $ EazyFun lst
        _ -> fail $ posToString pos ++ name ++ " is not defined"

deduceExprType (ExpIf pos texpr bexpr fexpr) = do -- OK
    bexprType <- deduceExprType bexpr
    -- TODO: Unify types
    ok <- unify bexprType EazyBool

    when (bexprType /= EazyBool) $
        fail $ posToString pos ++ "Expected boolean expression, got " ++ show bexprType
    fexprType <- deduceExprType fexpr
    texprType <- deduceExprType texpr
    -- TODO: Unify types
    ok <- unify texprType fexprType

    when (texprType /= fexprType) $
        fail $ posToString pos ++ "If branches have different types. Got " ++
            show texprType ++ " and " ++ show fexprType
    return texprType

deduceExprType (ExpOr pos expr expr') = deduceOpTypes pos EazyBool [expr, expr']

deduceExprType (ExpAnd pos expr expr') = deduceOpTypes pos EazyBool [expr, expr']

deduceExprType (ExpEqs pos expr _ expr') = do
    exprType <- deduceExprType expr -- TODO: check recursively for EazyFun to fail
    when (case exprType of {EazyFun _ -> True; _ -> False}) $
        fail $ posToString pos ++ "Cannot compare functions"
    exprType' <- deduceExprType expr'
    when (case exprType' of {EazyFun _ -> True; _ -> False}) $
        fail $ posToString pos ++ "Cannot compare functions"
    -- TODO: Unify types
    ok <- unify exprType exprType'

    when (exprType /= exprType') $
        fail $ posToString pos ++ "Cannot compare " ++ show exprType ++ " and " ++ show exprType'
    return EazyBool

deduceExprType (ExpCmp pos expr _ expr') = do
    exprType <- deduceExprType expr
    -- TODO: Unify types
    ok1 <- unify exprType EazyInt

    when (exprType /= EazyInt) $
        fail $ posToString pos ++ "Expected integer expression, got " ++ show exprType
    exprType' <- deduceExprType expr'
    -- TODO: Unify types
    ok2 <- unify exprType' EazyInt

    when (exprType' /= EazyInt) $
        fail $ posToString pos ++ "Expected integer expression, got " ++ show exprType'
    return EazyBool

deduceExprType (ExpAdd pos expr _ expr') = deduceOpTypes pos EazyInt [expr, expr']

deduceExprType (ExpMul pos expr _ expr') = deduceOpTypes pos EazyInt [expr, expr']

deduceExprType (ExpNot pos expr) = deduceOpTypes pos EazyBool [expr]

deduceExprType (ExpNeg pos expr) = deduceOpTypes pos EazyInt [expr]

deduceExprType (ExpChn pos expr expr') = do
    expr'Type <- deduceExprType expr'
    exprType <- deduceExprType expr
    -- TODO: Unify types
    ok <- unify exprType expr'Type

    when (expr'Type /= EazyList exprType) $
        fail $ posToString pos ++ "Expected list of " ++ show exprType ++ ", got " ++ show expr'Type
    return $ EazyList exprType

deduceExprType (ExpLst pos exprs) = case exprs of
    [] -> getT <&> (EazyList . EazyVar)
    [expr] -> do
        exprType <- deduceExprType expr
        return $ EazyList exprType
    h:t -> do
        hType <- deduceExprType h
        deduceOpTypes pos hType t
        return $ EazyList hType

deduceExprType (ExpLet _ decls expr) = do
    env <- getE
    mapM_ (translate False) decls -- TODO: ignore global types ...
    exprType <- deduceExprType expr
    putE env
    return exprType

deduceExprType (ExpLmb pos ty vis expr) = do
    env <- getE
    ts' <- getNT (1 + length vis)
    let ts = EazyVar <$> ts'
    putE $ foldr (\(VarIdent a, t) -> insert a (t, True)) env (zip vis ts)

    exprType <- deduceExprType expr
    -- read mappings
    updateM (last ts') exprType
    funType <- mapExpr (EazyFun ts)
    -- when (funType /= ty) $
    --     fail $ posToString pos ++ "Lambda has conflicting type. Got " ++
    --         show exprType ++ " and " ++ show expectedExprType
    putE env
    return funType

deduceExprType (ExpApp pos expr expr') = do
    exprType <- deduceExprType expr
    case exprType of
        EazyFun lst -> do
            expr'Type <- deduceExprType expr'
            case lst of
                [a, b] -> do
                    -- TODO: replace free variables

                    -- TODO: Unify types
                    ok <- unify expr'Type a
                    mapExpr b
                    -- if a == expr'Type
                    -- then return b -- use mappping
                    -- else case a of
                    --     EazyVar name -> return  $ subtypeWith (singleton name expr'Type) b
                    --     _ -> fail $ posToString pos ++ "Wrong type of argument. Expected " ++
                    --         show expr'Type ++ ", got " ++ show a
                a:t -> do
                    -- TODO: replace free variables

                    -- TODO: Unify types
                    ok <- unify expr'Type a
                    mapExpr $ EazyFun t
                    
                    -- if a == expr'Type  
                    -- then return $ EazyFun t -- use mappping
                    -- else case a of
                    --     EazyVar name -> return $ subtypeWith (singleton name expr'Type) $ EazyFun t
                    --     _ -> fail $ posToString pos ++ "Wrong type of argument. Expected " ++
                    --         show expr'Type ++ ", got " ++ show a
                _  -> fail $ posToString pos ++ "Unexpected error - 2"
        _ -> fail $ posToString pos ++ "Expected 0 arguments, got more"

deduceExprType (ExpMth _ expr matchings) = do
    exprType' <- deduceExprType expr
    exprType <- foldM (\t (MatchT p pat _) -> do
        patType <- deducePatternType pat
        -- TODO: Unify types
        ok <- unify t patType

        -- when (patType /= exprType) $
        --     fail $ posToString p ++ "Error in pattern type. Expected " ++
        --         show exprType ++ ", got " ++ show patType

        return patType
        
        ) exprType' matchings

    start <- getT <&> EazyVar
    foldM (\t (MatchT p apat e) -> do
        env <- getE
        case apat of
            PatAs _ pat (VarIdent v) -> do
                putE $ insert v (exprType, True) env
                enrichEnvWithPat pat exprType
            Pat _ pat -> enrichEnvWithPat pat exprType

        resExprType <- deduceExprType e
        -- TODO: Unify types
        ok <- unify resExprType t

        putE env
        return resExprType

        ) start matchings

-- TODO: manage OK's and errors
unify :: EazyType -> EazyType -> StateT TypeEnv Err (Maybe EazyType)
unify (EazyVar a) (EazyVar b) = undefined
unify (EazyVar a) t = undefined
unify t (EazyVar b) = unify (EazyVar b) t
-- List with EazyVar?
-- Con with EazyVar?
-- EazyFun with EazyVar?
unify a b = return Nothing

-- Use a map to replace free variables with locally sensible type
-- TODO: change so it uses getT ?
subtypeWith :: Map String EazyType -> EazyType -> EazyType
subtypeWith repl (EazyVar s) = case repl !? s of {Nothing -> EazyVar s; Just t -> t}
subtypeWith repl (EazyList nt) = EazyList $ subtypeWith repl nt
subtypeWith repl (EazyCon s nts) = EazyCon s $ map (subtypeWith repl) nts
subtypeWith repl (EazyFun nts) = EazyFun $ map (subtypeWith repl) nts
subtypeWith _ res = res

enrichEnvWithPat :: Pattern' BNFC'Position -> EazyType -> StateT TypeEnv Err ()
enrichEnvWithPat (PatVar _ (VarIdent  v)) t = do
    env <- getE
    putE $ insert v (t, True) env
enrichEnvWithPat (PatCon _ (ConIdent name) sps) (EazyCon con ts) = do
    env <- getE
    let (EazyFun args', _) = env ! name -- e.g. Leaf a -> Tree a
    let (EazyCon _ names', _) = env ! con -- e.g. Tree a
    let names = map (\(EazyVar v) -> v) names' -- TODO: create resonable mapping to types from stream
    let m = foldl (\m (n, t) -> insert n t m) empty (zip names ts) 
    let args = map (subtypeWith m) args'
    mapM_ (\(t, SubPatT _ p) -> enrichEnvWithPat p t) (zip args sps)
enrichEnvWithPat (PatLL _ pat pat') (EazyList t) =
    enrichEnvWithPat pat t >> enrichEnvWithPat pat' (EazyList t)
enrichEnvWithPat (PatLst _ pats) (EazyList t) = mapM_ (`enrichEnvWithPat` t) pats
enrichEnvWithPat (PatLit _ _) t = return ()
enrichEnvWithPat (PatDef _) t = return ()
enrichEnvWithPat p t = fail $ "Unexpected pattern: " ++ show p ++ " with type " ++ show t

deducePatternType :: AbsPattern' BNFC'Position -> StateT TypeEnv Err EazyType
deducePatternType pat =
    let aux :: Pattern' BNFC'Position -> StateT TypeEnv Err EazyType
        aux (PatCon pos (ConIdent name) sps) = do
            env <- getE
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
            [] -> getT <&> (EazyList . EazyVar)
            [p] -> aux p <&> EazyList
            h:t -> do
                expPatType <- aux h
                mapM_ (\e -> do
                    patType <- aux e
                    when (patType /= expPatType) $ conflictError pos expPatType patType
                    ) t
                return $ EazyList expPatType
        aux (PatLit _ lit) = return $ case lit of {LitInt _ _ -> EazyInt; _ -> EazyBool}
        aux (PatVar _ _) = getT <&> EazyVar
        aux (PatDef _) = getT <&> EazyVar
    in case pat of
        PatAs _ pat' _ -> aux pat'
        Pat _ pat' -> aux pat'

-- Replacing free variables in patterns
subtypeConPat :: BNFC'Position -> (EazyType, Map String EazyType) -> (EazyType, EazyType) ->
            StateT TypeEnv Err (EazyType, Map String EazyType)
subtypeConPat pos (arg, m) (t, next) = case t of -- t - jaki powinien być, arg - jaki jest w envie
    EazyInt -> case arg of -- TODO: clean up by starting with case arg first
        EazyVar s -> let m = insert s t m in -- TODO: REMOVE THOSE RECURSIVE LIES!!!
            return (subtypeWith m next, m)
        EazyInt -> return (subtypeWith m next, m)
        _ -> conflictError pos arg t
    EazyBool -> case arg of
        EazyVar s -> let m = insert s t m in
            return (subtypeWith m next, m)
        EazyBool -> return (subtypeWith m next, m)
        _ -> conflictError pos arg t
    EazyVar s -> let m = insert s t m in return (subtypeWith m next, m)
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

deduceOpTypes :: BNFC'Position -> EazyType -> [Expr' BNFC'Position] -> StateT TypeEnv Err EazyType
deduceOpTypes pos =
    foldM (\ext e -> do
        t <- deduceExprType e
        -- TODO: Unify types
        ok <- unify ext t

        -- case t of
        --     EazyVar s -> updateM s exType
        --     _ -> when (t /= exType) $ fail $ posToString pos ++
        --         "Expected expression of type " ++ show exType ++ ", got " ++ show t

        return t
    )


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
    env <- getE
    when (fname `member` env) $
        fail $ posToString pos ++ "Constructor " ++ fname ++ " is already defined"
    types <- mapM translateFunT types

    let varSet = Set.fromList $ map (\(VarIdent n) -> n) args
    mapM_ (\(a, _) -> errorIfNewVars pos varSet a) types

    let fun = EazyFun ((fst <$> types) ++ [EazyCon tname (devarify <$> args )])
    putE $ insert fname (fun, True) env

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
        env <- getE
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
        env <- getE
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
