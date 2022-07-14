{-# LANGUAGE LambdaCase #-}
module TypeChecker (typeCheck) where

import Eazy.ErrM (Err)
import Eazy.Abs
import Control.Monad (foldM, when, unless, zipWithM, zipWithM_)
import Control.Monad.Trans.State (execStateT, get, put, StateT, gets, modify)
import Data.Map (empty, Map, member, insert, (!?), (!), filter, keys, foldrWithKey, toList)
import Data.List (nub, transpose)
import qualified Data.Set as Set
import Data.Functor ((<&>))
import Data.Maybe (catMaybes, isNothing, fromJust, isJust)
import Data.Foldable (foldrM)

data EazyType =
    EazyInt  |
    EazyBool |
    EazyVar String |
    EazyList EazyType |
    EazyCon String [EazyType] |
    EazyFun [EazyType] deriving (Show)

type TypeDef = (EazyType, Bool)

instance Eq EazyType where
    EazyInt == EazyInt = True
    EazyBool == EazyBool = True
    EazyVar x == EazyVar y = x == y
    EazyList x == EazyList y = x == y
    EazyCon x y == EazyCon z u = x == z && fst (fvEq empty empty y u)
    EazyFun x == EazyFun y = fst (fvEq empty empty x y)
    _ == _ = False

fvEq :: Map String String -> Map String String -> [EazyType] -> [EazyType] ->
    (Bool, (Map String String, Map String String))
fvEq ml mr l r = if length l /= length r then (False, (ml, mr)) else foldr (\el (eq, (ml, mr)) ->
    if eq then case el of
        (EazyCon lx ly, EazyCon rx ry) -> if lx == rx then fvEq ml mr ly ry else (False, (ml, mr))
        (EazyFun l, EazyFun r) -> fvEq ml mr l r
        (EazyVar l, EazyVar r) -> if l `member` ml
            then if r `member` mr
                then (ml ! l == r && mr ! r == l, (ml, mr))
                else (False, (ml, mr))
            else if r `member` mr
                then (False, (ml, mr))
                else (True, (insert l r ml, insert r l mr))
        (l, r) -> (l == r, (ml, mr))
    else (False, (ml, mr))
    ) (True, (ml, mr)) (zip l r)

tStream :: [String]
tStream = let aux n = show n : aux (n + 1) in aux 0

type TypeEnv = (Map String TypeDef, (IO(), ([String], String -> Maybe EazyType)))

type EnvM a = StateT TypeEnv Err a

emptyEnv :: TypeEnv
emptyEnv = (empty, (putStr "", (tStream, const Nothing)))

getE :: Monad m => StateT (s, a) m s
getE = gets fst

putE :: Monad m => s -> StateT (s, a) m ()
putE = modify . (. snd) . (,)

warning :: String -> EnvM ()
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

translate :: Bool -> Decl -> EnvM ()
translate isTop (DeclFunT pos (VarIdent name) ty) = do
    unless isTop $ fail "Typing inside of let expressions not allowed"
    env <- getE
    pTy@(ty', defined) <- translateFunT ty
    when (name `member` env) $ if defined
        then
            unless (fst (env ! name) == ty') $ fail $ posToString pos ++
                "Function " ++ name ++ " already defined with different type"
        else
            fail $ posToString pos ++ "Function " ++ name ++ " is already declared"
    putE $ insert name pTy env

translate isTop (DeclData pos (SimpleTypeT _ (ConIdent tname) params) cons) = do
    env <- getE
    when (tname `member` env) $
        fail $ posToString pos ++ "Type " ++ tname ++ " is already defined"
    when (length (nub params) /= length params) $
        fail $ posToString pos ++ "Conflicting parameter names in type " ++ tname
    putE $ insert tname (EazyCon tname (devarify <$> params), True) env
    foldM (`translateDataT` (tname,  params)) () cons

translate isTop (DeclFunc pos (VarIdent name) args expr) = do
    env <- getE
    when (length (nub args) /= length args) $
        fail $ posToString pos ++ "Conflicting arguments in " ++ name
    ts' <- getNT (1 + length args)
    let ts = EazyVar <$> ts'
    putE $ insert name (EazyFun ts, True) (
        foldr (\(VarIdent a, t) -> insert a (t, True)) env (zip args ts))
    exprType'silence_warn <- deduceExprType expr
    -- extract mappings for ts
    updateM (last ts') exprType'silence_warn
    funType <- mapExpr (EazyFun ts)
    -- if defined and not equal then error else add type to env
    case (env !? name, isTop) of
        (Nothing, _) -> putE $ insert name (funType, True) env
        (Just (et, True), True) -> fail $ posToString pos ++ "Function " ++ name ++ " is already defined"
        (Just (et, _), _) -> do
            ok <- unify funType et
            when (isNothing ok) $ fail $ posToString pos ++
                "Type mismatch in " ++ name ++ ": " ++ show et ++ " != " ++ show funType
            putE $ insert name (fromJust ok, True)  env

    -- if top_translate then reset Types and mappings else do nothing
    when isTop resetT

mapExpr :: EazyType -> EnvM EazyType
mapExpr et = case et of
    EazyVar v -> getM v >>= \case {Just t -> return t; Nothing -> return $ EazyVar v}
    EazyList et -> mapExpr et <&> EazyList
    EazyCon s ets -> mapM mapExpr ets <&> EazyCon s
    EazyFun ets -> mapM mapExpr ets <&> (\case {[a] -> a; ets' -> EazyFun ets'})
    t -> return t

deduceExprType :: Expr' BNFC'Position -> EnvM EazyType
deduceExprType (ExpLit _ lit) = return $ case lit of
    LitInt _ _ ->  EazyInt
    _ -> EazyBool

deduceExprType (ExpVar pos (VarIdent name)) = do
    env <- getE
    case env !? name of
        Just (t@(EazyFun _), _) -> replaceFV t
        Just (EazyVar v, _) -> getM v <&> (\case {Just t -> t; Nothing -> EazyVar v})
        Just (t, True) -> return t
        _ -> fail $ posToString pos ++ "\"" ++ name ++ "\" is not defined"

deduceExprType (ExpCon pos (ConIdent name)) = do
    env <- getE
    case env !? name of
        Just (EazyFun lst, True) -> case lst of
            [t] -> replaceFV t
            [] -> fail $
                posToString pos ++ "Unexpected error - Constructor " ++ name ++ " has no type"
            _ -> replaceFV $ EazyFun lst
        _ -> fail $ posToString pos ++ name ++ " is not defined"

deduceExprType (ExpIf pos texpr bexpr fexpr) = do
    bexprType <- deduceExprType bexpr
    -- Unify types
    ok1 <- unify bexprType EazyBool
    when (isNothing ok1) $
        fail $ posToString pos ++ "Expected boolean expression, got " ++ show bexprType

    fexprType <- deduceExprType fexpr
    texprType <- deduceExprType texpr
    -- Unify types
    ok2 <- unify texprType fexprType

    when (isNothing ok2) $
        fail $ posToString pos ++ "If branches have conflicting types. Got " ++
            show texprType ++ " and " ++ show fexprType

    return $ fromJust ok2

deduceExprType (ExpOr pos expr expr') = deduceOpTypes pos EazyBool [expr, expr']

deduceExprType (ExpAnd pos expr expr') = deduceOpTypes pos EazyBool [expr, expr']

deduceExprType (ExpEqs pos expr _ expr') = do
    exprType <- deduceExprType expr
    exprType' <- deduceExprType expr'
    -- Unify types
    ok <- unify exprType exprType'

    when (isNothing ok) $
        fail $ posToString pos ++ "Cannot compare " ++ show exprType ++ " and " ++ show exprType'

    when (hasUncomparable $ fromJust ok) $
        fail $ posToString pos ++ "Cannot compare elements of type " ++ show exprType

    return EazyBool
    where
        hasUncomparable :: EazyType -> Bool
        hasUncomparable (EazyFun _) = True
        hasUncomparable (EazyList et) = hasUncomparable et
        hasUncomparable (EazyCon _ ets) = any hasUncomparable ets
        hasUncomparable _ = False

deduceExprType (ExpCmp pos expr _ expr') = do
    exprType <- deduceExprType expr
    -- Unify types
    ok1 <- unify exprType EazyInt

    when (isNothing ok1) $
        fail $ posToString pos ++ "Expected integer expression, got " ++ show exprType

    exprType' <- deduceExprType expr'
    -- Unify types
    ok2 <- unify exprType' EazyInt

    when (isNothing ok2) $
        fail $ posToString pos ++ "Expected integer expression, got " ++ show exprType'
    return EazyBool

deduceExprType (ExpAdd pos expr _ expr') = deduceOpTypes pos EazyInt [expr, expr']

deduceExprType (ExpMul pos expr _ expr') = deduceOpTypes pos EazyInt [expr, expr']

deduceExprType (ExpNot pos expr) = deduceOpTypes pos EazyBool [expr]

deduceExprType (ExpNeg pos expr) = deduceOpTypes pos EazyInt [expr]

deduceExprType (ExpChn pos expr expr') = do
    expr'Type <- deduceExprType expr'
    exprType <- deduceExprType expr
    -- Unify types
    ok <- unify (EazyList exprType) expr'Type

    when (isNothing ok) $
        fail $ posToString pos ++ "Expected list of " ++ show exprType ++ ", got " ++ show expr'Type

    return $ fromJust ok

deduceExprType (ExpLst pos exprs) = case exprs of
    [] -> getT <&> (EazyList . EazyVar)
    [expr] -> deduceExprType expr <&> EazyList
    h:t -> do
        hType <- deduceExprType h
        deduceOpTypes pos hType t <&> EazyList

deduceExprType (ExpLet _ decls expr) = do
    env <- getE
    mapM_ (translate False) decls
    exprType <- deduceExprType expr
    putE env
    return exprType

deduceExprType (ExpLmb pos vis expr) = do
    env <- getE
    ts' <- getNT (1 + length vis)
    let ts = EazyVar <$> ts'
    putE $ foldr (\(VarIdent a, t) -> insert a (t, True)) env (zip vis ts)
    exprType <- deduceExprType expr
    updateM (last ts') exprType
    funType <- mapExpr (EazyFun ts)
    putE env
    return funType

deduceExprType (ExpApp pos expr expr') = do
    exprType <- deduceExprType expr
    case exprType of
        EazyFun lst -> do
            expr'Type <- deduceExprType expr'
            case lst of
                [a, b] -> do
                    -- Unify types
                    ok <- unify expr'Type a
                    when (isNothing ok) $
                        fail $ posToString pos ++ "Wrong type of argument. Expected " ++
                            show a ++ ", got " ++ show expr'Type
                    mapExpr b
                a:t -> do
                    -- Unify types
                    ok <- unify expr'Type a
                    when (isNothing ok) $
                        fail $ posToString pos ++ "Wrong type of argument. Expected " ++
                            show a ++ ", got " ++ show expr'Type
                    mapExpr $ EazyFun t
                _  -> fail $ posToString pos ++ "Unexpected error - unexpected arguments"
        EazyVar a -> do
            expr'Type <- deduceExprType expr'
            nt' <- getT
            ok <- unify exprType (EazyFun [expr'Type, EazyVar nt'])
            nt <- mapExpr $ EazyVar nt'
            when (isNothing ok) $
                fail $ posToString pos ++ "Wrong type of argument. Expected " ++
                    show (EazyFun [expr'Type, nt]) ++ ", got " ++ show exprType
            return nt

        _ -> fail $ posToString pos ++ "Expected 0 arguments, got more"

deduceExprType (ExpMth pos expr ms) = do
    exprType' <- deduceExprType expr
    exprType <- foldM (\t (MatchT p pat _) -> do
        patType <- deducePatternType pat
        -- Unify types
        ok <- unify patType t

        when (isNothing ok) $
            fail $ posToString p ++ "Conflict in pattern type. Expected " ++
                show t ++ ", got " ++ show patType

        return $ fromJust ok
        ) exprType' ms
    c <- matchComplete exprType ((\(MatchT _ a _) -> case a of {PatAs _ p _ -> p; Pat _ p -> p }) <$> ms)
    when (not c && pos /= Just (0,0)) $
        warning $ posToString pos ++ "Incomplete pattern match"

    start <- getT <&> EazyVar
    foldM (\t (MatchT p apat e) -> do
        env <- getE
        case apat of
            PatAs _ pat (VarIdent v) -> do
                putE $ insert v (exprType, True) env
                enrichEnvWithPat pat exprType
            Pat _ pat -> enrichEnvWithPat pat exprType

        resExprType <- deduceExprType e

        -- Unify types
        ok <- unify resExprType t
        when (isNothing ok) $
            fail $ posToString p ++ "Conflicting expression types in match. Expected " ++
                show t ++ ", got " ++ show resExprType

        putE env
        return $ fromJust ok
        ) start ms

matchComplete :: EazyType -> [Pattern' BNFC'Position] -> EnvM Bool
matchComplete (EazyVar s) ps = return True
matchComplete EazyInt ps = return $ hasSink ps
matchComplete EazyBool ps = return (hasSink ps ||
    (any (\case {PatLit _ (LitTrue _)  -> True; _ -> False}) ps &&
        any (\case {PatLit _ (LitFalse _) -> True; _ -> False}) ps))
matchComplete (EazyList et) ps = return (hasSink ps ||
    (any (\case {PatLst _ []  -> True; _ -> False}) ps &&
        any (\case {PatLL _ a b -> hasSink [a] && hasSink [b]; _ -> False}) ps))
matchComplete (EazyCon s ets) ps = if hasSink ps then return True else do
    env <- getE
    let x = Data.Map.filter (\case {(EazyFun a, _) -> case last a of {
            (EazyCon s' ets') -> s' == s;
            _ -> False
        }; _ -> False }) env
    foldM (\b (k, (EazyFun args', _)) -> if not b then return False else
        let cons = Prelude.filter (\case PatCon _ (ConIdent c) sps -> c == k; _ -> False) ps
        in if null cons then return False else
        let pats = transpose $ map (\case {
            PatCon _ (ConIdent c) sps -> (\case SubPatT _ p -> p ) <$> sps; _ -> undefined
            }) cons
        in do
            when (s == "Node") $ fail $ show x ++ "\n\n" ++ show cons ++ "\n\n" ++ show pats
            let (EazyCon _ names', _) = env ! s
            let names = map (\(EazyVar v) -> v) names'
            let m = foldl (\m (n, t) -> insert n t m) empty (zip names ets)
            let args = map (subtypeWith m) args'
            zipWithM matchComplete args pats <&> and
        ) True (toList x)

matchComplete (EazyFun ets) _ = fail "Unexpected error - no pattern matching for functions."

hasSink :: [Pattern' BNFC'Position] -> Bool
hasSink = any (\case {PatDef _ -> True; PatVar _ _ -> True; _ -> False})

replaceFV :: EazyType -> EnvM EazyType
replaceFV = let
    aux :: Map String EazyType -> EazyType -> EnvM (EazyType, Map String EazyType)
    aux m EazyInt = return (EazyInt, m)
    aux m EazyBool = return (EazyBool, m)
    aux m (EazyVar s) = if s `member` m
        then return (m ! s, m)
        else getT <&> ((\x -> (x, insert s x m)) . EazyVar)
    aux m' (EazyList et') = aux m' et' >>= \(et, m) -> return (EazyList et, m)
    aux m'' (EazyCon s ets) = foldrM (\t' (EazyCon _ ts, m') -> do
        (t, m) <- aux m' t'
        return (EazyCon s (t:ts), m)) (EazyCon s [], m'') ets
    aux m'' (EazyFun ets) = foldrM (\t' (EazyFun ts, m') -> do
        (t, m) <- aux m' t'
        return (EazyFun (t:ts), m)) (EazyFun [], m'') ets
    in fstM . aux empty

unify :: EazyType -> EazyType -> EnvM (Maybe EazyType)
unify (EazyVar a) x@(EazyVar b) = return $ Just x
unify x@(EazyVar a) b =  getM a >>= \case
    Nothing -> if b /= x && hasType x b then return Nothing else updateM a b >> return (Just b)
    Just et -> updateM a b >> unify et b
unify t (EazyVar b) = unify (EazyVar b) t
unify (EazyList a) (EazyList b) = unify a b <&> (\case {Just t -> Just $ EazyList t; _ -> Nothing})
unify (EazyCon a as) (EazyCon b bs) = if a /= b then return Nothing else
    zipWithM unify as bs <&> (\l -> if any isNothing l then Nothing else Just $ EazyCon a $ catMaybes l)
unify (EazyFun a') (EazyFun b') = let a = cutTails a'; b = cutTails b'; diff = length a - length b
    in if diff < 0 then unify (EazyFun b) (EazyFun a)
    else if diff > 0 then do
        updateM ((\(EazyVar x) -> x) $ last b) (EazyFun $ drop (length b - 1) a)
        r <- getM ((\(EazyVar x) -> x) $ last b)
        ra <- mapExpr (EazyFun a)
        rb <- mapExpr (EazyFun b)
        unify ra rb
    else
    zipWithM unify a b <&> (\l -> if any isNothing l then Nothing else Just $ EazyFun $ catMaybes l)
unify EazyInt EazyInt = return $ Just EazyInt
unify EazyBool EazyBool = return $ Just EazyBool
unify a b = return Nothing

cutTails :: [EazyType] -> [EazyType]
cutTails = \case
    [] -> []
    [EazyFun ets] -> cutTails ets
    h:t -> h:cutTails t

hasType :: EazyType -> EazyType -> Bool
hasType needle haystack = case haystack of
    EazyInt -> needle == EazyInt
    EazyBool -> needle == EazyBool
    EazyVar s -> needle == EazyVar s
    EazyList ht -> case needle of
        EazyList nt -> hasType nt ht
        _ -> hasType needle ht
    EazyCon s hts -> case needle of
        EazyCon ns nts -> if s == ns
            then all (uncurry hasType) (zip nts hts)
            else any (hasType needle) hts
        _ -> any (hasType needle) hts
    EazyFun hts -> case needle of
        EazyFun nts -> if length nts == length hts
            then any (hasType needle) hts || all (uncurry hasType) (zip nts hts)
            else any (hasType needle) hts
        _ -> any (hasType needle) hts

subtypeWith :: Map String EazyType -> EazyType -> EazyType
subtypeWith repl (EazyVar s) = case repl !? s of {Nothing -> EazyVar s; Just t -> t}
subtypeWith repl (EazyList nt) = EazyList $ subtypeWith repl nt
subtypeWith repl (EazyCon s nts) = EazyCon s $ map (subtypeWith repl) nts
subtypeWith repl (EazyFun nts) = EazyFun $ map (subtypeWith repl) nts
subtypeWith _ res = res

enrichEnvWithPat :: Pattern' BNFC'Position -> EazyType -> EnvM ()
enrichEnvWithPat (PatDef _) t = return ()
enrichEnvWithPat (PatLit _ _) t = return ()
enrichEnvWithPat (PatVar _ (VarIdent  v)) t = do
    env <- getE
    putE $ insert v (t, True) env
enrichEnvWithPat p (EazyVar v) = case p of
    PatCon _ (ConIdent n) sps -> do
        nts' <- getNT (length sps)
        let nts = map EazyVar nts'
        updateM v (EazyCon n nts)
        enrichEnvWithPat p (EazyCon n nts)
    PatLit _ lit -> return ()
    PatVar _ vi -> return ()
    PatDef _ -> return ()
    _ -> do -- Lists
        nt <- getT <&> EazyVar
        updateM v (EazyList nt)
        env <- getE
        enrichEnvWithPat p (EazyList nt)
enrichEnvWithPat (PatCon _ (ConIdent name) sps) (EazyCon con ts) = do
    env <- getE
    let (EazyFun args', _) = env ! name -- e.g. Leaf a -> Tree a
    let (EazyCon _ names', _) = env ! con -- e.g. Tree a
    let names = map (\(EazyVar v) -> v) names'
    let m = foldl (\m (n, t) -> insert n t m) empty (zip names ts)
    let args = map (subtypeWith m) args'
    mapM_ (\(t, SubPatT _ p) -> enrichEnvWithPat p t) (zip args sps)
enrichEnvWithPat (PatLL _ pat pat') (EazyList t) =
    enrichEnvWithPat pat t >> enrichEnvWithPat pat' (EazyList t)
enrichEnvWithPat (PatLst _ pats) (EazyList t) = mapM_ (`enrichEnvWithPat` t) pats
enrichEnvWithPat p t = fail $ "Unexpected pattern: " ++ show p ++ " with type " ++ show t

deducePatternType :: AbsPattern' BNFC'Position -> EnvM EazyType
deducePatternType = let
    aux :: Pattern' BNFC'Position -> EnvM EazyType
    aux (PatDef _) = getT <&> EazyVar
    aux (PatVar _ _) = getT <&> EazyVar
    aux (PatLit _ lit) = return $ case lit of {LitInt _ _ -> EazyInt; _ -> EazyBool}
    aux (PatCon pos (ConIdent name) sps) = deduceExprType (ExpCon pos (ConIdent name)) >>= \case
        EazyFun types -> mapM (\(SubPatT _ p) -> aux p) sps >>=
            zipWithM_ unify types >>
            mapExpr (last types)
        c -> return c
    aux (PatLL pos pat1 pat2) = do
        pat2Type <- aux pat2
        pat1Type <- aux pat1
        ok <- unify (EazyList pat1Type) pat2Type
        when (isNothing ok) $ conflictError pos pat1Type pat2Type
        return $ fromJust ok
    aux (PatLst pos pats) = case pats of
        [] -> getT <&> (EazyList . EazyVar)
        [p] -> aux p <&> EazyList
        h:t -> do
            expPatType <- aux h
            foldM (\ext e -> do
                patType <- aux e
                ok <- unify patType ext
                when (isNothing ok) $ conflictError pos patType ext
                return $ fromJust ok
                ) expPatType t <&> EazyList
    in \case {PatAs _ pat _ -> aux pat; Pat _ pat -> aux pat}

conflictError :: MonadFail m => BNFC'Position -> EazyType -> EazyType -> m a
conflictError pos arg1 arg2 = fail $ posToString pos ++ "Conflicting pattern types. Got " ++
    show arg1 ++ " and " ++ show arg2

deduceOpTypes :: BNFC'Position -> EazyType -> [Expr' BNFC'Position] -> EnvM EazyType
deduceOpTypes pos =
    foldM (\ext e -> do
        t <- deduceExprType e
        -- Unify types
        ok <- unify t ext
        when (isNothing ok) $ fail $ posToString pos ++
            "Expected expression of type " ++ show ext ++ ", got " ++ show t
        return $ fromJust ok
    )

translateDataT :: () -> (String, [VarIdent]) -> Constr' BNFC'Position -> EnvM ()
translateDataT _ (tname, args) (ConstrT pos (ConIdent fname) types) = do
    env <- getE
    when (fname `member` env) $
        fail $ posToString pos ++ "Constructor " ++ fname ++ " is already defined"
    types <- mapM translateFunT types

    let varSet = Set.fromList $ map (\(VarIdent n) -> n) args
    mapM_ (\(a, _) -> errorIfNewVars pos varSet a) types

    let fun = EazyFun ((fst <$> types) ++ [EazyCon tname (devarify <$> args)])
    putE $ insert fname (fun, True) env

errorIfNewVars :: BNFC'Position -> Set.Set String -> EazyType -> EnvM ()
errorIfNewVars pos set t = case t of
    EazyVar str -> unless (str `Set.member` set) $
        fail $ posToString pos ++ "Unrecognised variable " ++ str
    EazyList nt -> errorIfNewVars pos set nt
    EazyCon _ nts -> mapM_ (errorIfNewVars pos set) nts
    EazyFun nts -> mapM_ (errorIfNewVars pos set) nts
    _ -> return ()

devarify :: VarIdent -> EazyType
devarify (VarIdent n) = EazyVar n

translateFunT :: Type' BNFC'Position -> EnvM TypeDef
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

tail' :: BNFC'Position -> [EazyType] -> EnvM [EazyType]
tail' pos [] = fail $ posToString pos ++ "Wrong number of argmuents"
tail' pos (a:as) = return as

getTlist :: TypeDef -> [EazyType]
getTlist (EazyFun l, _) = l
getTlist (other, _) = [other]
