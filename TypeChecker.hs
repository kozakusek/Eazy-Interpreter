module TypeChecker (typeCheck) where

import Eazy.ErrM (Err)
import Eazy.Abs
import Control.Monad (foldM, when, unless, void, replicateM, foldM_)
import Control.Monad.Trans.State (execStateT, get, put, StateT, gets, modify)
import Data.Map.Lazy (empty, Map, member, insert, (!?), (!), adjust)
import Data.List (nub)
import qualified Data.Set as Set
import Data.Functor ((<&>))

data EazyType =
    EazyInt  |
    EazyBool |
    EazyNil  | -- not correct final type?
    EazyVar String |
    EazyList EazyType |
    EazyCon String [EazyType] |
    EazyFun [EazyType] deriving (Show, Ord)

data PromiseT =
    Fulfilled EazyType Bool  | XD deriving (Show)
    --Pending Expr TypeEnv deriving 

type TypeEnv = (Map String PromiseT, IO())

instance Eq EazyType where
    EazyInt == EazyInt = True
    EazyBool == EazyBool = True
    EazyNil == _ = True
    _ == EazyNil = True
    EazyVar x == EazyVar y = x == y -- does it really work this way?
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
    warning "TypeChecker is not implemented yet"
    case decl of
        DeclFunT pos (VarIdent name) ty -> do
            env <- wget
            pTy@(Fulfilled ty' _) <- translateFunT ty
            checkLast pos ty'
            wput $ insert name pTy env -- Allowing shadowing
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
            -- Allowing shadowing
            when (length (nub args) /= length args) $
                fail $ posToString pos ++ "Conflicting arguments in " ++ name
            let tname = env ! name
            expectedExprType <- forseeExprType pos args tname
            wput $ adjust (\(Fulfilled t False) -> Fulfilled t True) name (
                foldr (\(VarIdent a, t) -> insert a (Fulfilled t True)) env (zip args (getTlist tname)))
            exprType <- deduceExprType expr
            when (exprType /= expectedExprType) $
                fail $ posToString pos ++ "Function " ++ name ++ show args ++ " has wrong type" ++
                    "\n\tExpected: " ++ show expectedExprType ++
                    "\n\tActual: " ++ show exprType
            wput $ adjust (\(Fulfilled t False) -> Fulfilled t True) name env

getTlist :: PromiseT -> [EazyType]
getTlist (Fulfilled (EazyFun l) _) = l
getTlist (Fulfilled other _) = [other]
getTlist _ = []

deduceExprType :: Expr' BNFC'Position -> StateT TypeEnv Err EazyType
deduceExprType (ExpLit _ lit) = return $ case lit of
    LitInt _ v ->  EazyInt
    _ -> EazyBool

deduceExprType (ExpVar pos (VarIdent name)) = do -- TODO: EazyNil and reconstruction
    env <- wget
    --when (name == "fibonacci") $ fail $ show env
    case env !? name of
        Just (Fulfilled t True) -> return t
        Nothing -> return EazyNil
        _ -> fail $ posToString pos ++ name ++ " is not defined"

deduceExprType (ExpCon pos (ConIdent name)) = do
    env <- wget
    case env !? name of
        Just (Fulfilled (EazyFun lst) True) -> case lst of
            [t] -> return t
            [] -> fail $ posToString pos ++ "Unexpected error"
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

deduceExprType (ExpCmp pos expr cop expr') = (case cop of
    (OpEq _) -> do
        exprType <- deduceExprType expr
        deduceOpTypes exprType pos [expr']
    (OpNeq _)-> do
        exprType <- deduceExprType expr
        deduceOpTypes exprType pos [expr']
    _ ->  deduceOpTypes EazyInt pos [expr, expr']) >> return EazyBool

deduceExprType (ExpAdd pos expr _ expr') = deduceOpTypes EazyInt pos [expr, expr']

deduceExprType (ExpMul pos expr _ expr') = deduceOpTypes EazyInt pos [expr, expr']

deduceExprType (ExpNot pos expr) = deduceOpTypes EazyBool pos [expr]

deduceExprType (ExpNeg pos expr) = deduceOpTypes EazyInt pos [expr]

deduceExprType (ExpChn pos expr expr') = do -- TODO: EazyNil and reconstruction
    exprType <- deduceExprType expr
    expr'Type <- deduceExprType expr'
    when (expr'Type /= EazyList exprType) $
        fail $ posToString pos ++ "Expected list of " ++ show exprType ++ ", got " ++ show expr'Type
    return $ EazyList exprType

deduceExprType (ExpLst pos exprs) = case exprs of
    [] -> return $ EazyList EazyNil -- TODO: EazyNil and reconstruction
    [expr] -> do
        exprType <- deduceExprType expr
        return $ EazyList exprType
    h:t -> do
        hType <- deduceExprType h
        deduceOpTypes hType pos t

deduceExprType (ExpLet _ decls expr) = do -- TODO: allow shadowing
    env <- wget
    foldM_ (\_ d -> translate d) () decls
    exprType <- deduceExprType expr
    wput env
    return exprType

deduceExprType (ExpLmb pos ty vis expr) = do
    pt@(Fulfilled lambdaType _) <- translateFunT ty
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
                [a, b] -> if a == expr'Type
                  then return b
                  else fail $ posToString pos ++ "Wrong type of argument. Expected " ++
                      show expr'Type ++ ", got " ++ show a
                a:t -> if a == expr'Type
                    then return $ EazyFun t
                    else fail $ posToString pos ++ "Wrong type of argument. Expected " ++
                        show expr'Type ++ ", got " ++ show a
                _  -> fail $ posToString pos ++ "Unexpected error"
        _ -> fail $ posToString pos ++ "Expected function, got " ++ show exprType

deduceExprType (ExpMth _ expr matchings) = do
    exprType <- deduceExprType expr
    foldM_ (\_ (MatchT p pat _) -> do
        patType <- deducePatternType pat
        when (patType /= exprType) $
            fail $ posToString p ++ "Error in pattern type. Expected " ++
                show exprType ++ ", got " ++ show patType
        ) () matchings
    -- TODO: Check for pattern type coverage
    foldM (\t (MatchT p pat e) -> do
        env <- wget
        case pat of
            PatAs _ _ (VarIdent v) -> wput $ insert v (Fulfilled exprType True) env
            _ -> return ()
        resExprType <- deduceExprType e
        wput env
        if t == EazyNil
            then return resExprType
            else fail $ posToString p ++ "Conflicting types. Expected " ++
                show t ++ ", got " ++ show resExprType
        ) EazyNil matchings

deducePatternType :: AbsPattern' BNFC'Position -> StateT TypeEnv Err EazyType
deducePatternType pat =
    let aux :: Pattern' BNFC'Position -> StateT TypeEnv Err EazyType
        aux pat = case pat of
            PatCon pos (ConIdent name) sps -> do
                env <- wget
                case env !? name of
                    Just (Fulfilled (EazyFun lst) _) -> case lst of
                        [t] -> return t
                        [] -> fail $ posToString pos ++ "Unexpected error"
                        _ -> do 
                            when (length sps + 1 /= length lst) $
                                fail $ posToString pos ++ "Wrong number of arguments."
                            types <- mapM (\(SubPatT _ pat, et) -> do
                                patType <- aux pat
                                
                                return et) (zip sps lst)
                            return $ EazyCon name types
                    _ -> fail $ posToString pos ++ name ++ " is not defined"
            PatLL pos pat1 pat2 -> do
                pat1Type <- aux pat1
                pat2Type <- aux pat2
                when (EazyList pat1Type /= pat2Type) $
                    fail $ posToString pos ++ "Conflicting pattern types. Got " ++
                        show pat1Type ++ " and " ++ show pat2Type
                return pat2Type
            PatLst pos pats -> case pats of
                [] -> return $ EazyList EazyNil
                [p] -> aux p <&> EazyList
                h:t -> do
                    expPatType <- aux h
                    mapM_ (\e -> do
                        patType <- aux e
                        when (patType /= expPatType) $
                            fail $ posToString pos ++ "Expected " ++ show expPatType ++ 
                                "patter, but got " ++ show patType
                        ) t
                    return $ EazyList expPatType
            PatLit _ lit -> return $ case lit of {LitInt _ _ -> EazyInt; _ -> EazyBool}
            PatVar _ _ -> return EazyNil
            PatDef _ -> return EazyNil
    in case pat of
        PatAs _ pat' _ -> aux pat'
        Pat _ pat' -> aux pat'

deduceOpTypes :: EazyType -> BNFC'Position -> [Expr' BNFC'Position] -> StateT TypeEnv Err EazyType
deduceOpTypes exType pos exprs = do
    mapM_ (\e -> do
        t <- deduceExprType e
        when (t /= exType) $
            fail $ posToString pos ++ "Expected boolean expression, got " ++ show t
        ) exprs
    return exType

forseeExprType :: BNFC'Position -> [VarIdent] -> PromiseT -> StateT TypeEnv Err EazyType
forseeExprType pos args promT = do
    case promT of
        Fulfilled (EazyFun l) _ -> do
            x <- foldM (\a e -> e a) l (replicate (length args) (tail' pos))
            case x of
                [a] -> return a
                [] -> fail $ posToString pos ++ "Unexpected error"
                _ -> return $ EazyFun x
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
--depromise (Pending _ ty) = EazyNil
depromise XD = EazyNil

devarify :: VarIdent -> EazyType
devarify (VarIdent n) = EazyVar n

translateFunT :: Type' BNFC'Position -> StateT TypeEnv Err PromiseT
translateFunT ty = case ty of
    TypCon _ (ConIdent "Integer") -> return $ Fulfilled EazyInt False
    TypCon _ (ConIdent "Bool")    -> return $ Fulfilled EazyBool False
    TypArr _ ty1 ty2 -> do
        Fulfilled ty1' _ <- translateFunT ty1
        Fulfilled ty2' _ <- translateFunT ty2
        -- let newTy = case (ty1', ty2') of
        --         (EazyFun x, EazyFun y) -> EazyFun (x ++ y)
        --         (EazyFun x, _) -> EazyFun (x ++ [ty2'])
        --         (_, EazyFun x) -> EazyFun (ty1':x)
        --         _ -> EazyFun [ty1', ty2']
        let newTy = case ty2' of
                EazyFun x -> EazyFun (ty1':x)
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
            EazyNil -> return ()
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