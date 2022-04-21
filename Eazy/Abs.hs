-- File generated by the BNF Converter (bnfc 2.9.4).

{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}

-- | The abstract syntax of language eazy.

module Eazy.Abs where

import Prelude (Integer, String)
import qualified Prelude as C
  ( Eq, Ord, Show, Read
  , Functor, Foldable, Traversable
  , Int, Maybe(..)
  )
import qualified Data.String

type Program = Program' BNFC'Position
data Program' a = ProgramT a [Decl' a]
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type Literal = Literal' BNFC'Position
data Literal' a = LitInt a Integer | LitTrue a | LitFalse a
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type SimpleType = SimpleType' BNFC'Position
data SimpleType' a = SimpleTypeT a ConIdent [VarIdent]
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type Constr = Constr' BNFC'Position
data Constr' a = ConstrT a ConIdent [Type' a]
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type Type = Type' BNFC'Position
data Type' a
    = TypArr a (Type' a) (Type' a)
    | TypApp a ConIdent (Type' a) [Type' a]
    | TypVar a VarIdent
    | TypCon a ConIdent
    | TypLst a (Type' a)
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type Decl = Decl' BNFC'Position
data Decl' a
    = DeclData a (SimpleType' a) [Constr' a]
    | DeclFunc a VarIdent [VarIdent] (Expr' a)
    | DeclFunT a VarIdent (Type' a)
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type Expr = Expr' BNFC'Position
data Expr' a
    = ExpIf a (Expr' a) (Expr' a) (Expr' a)
    | ExpMth a (Expr' a) [Match' a]
    | ExpLet a [Decl' a] (Expr' a)
    | ExpLmb a (Type' a) [VarIdent] (Expr' a)
    | ExpOr a (Expr' a) (Expr' a)
    | ExpAnd a (Expr' a) (Expr' a)
    | ExpCmp a (Expr' a) (CmpOp' a) (Expr' a)
    | ExpAdd a (Expr' a) (AddOp' a) (Expr' a)
    | ExpMul a (Expr' a) (MulOp' a) (Expr' a)
    | ExpChn a (Expr' a) (Expr' a)
    | ExpNot a (Expr' a)
    | ExpNeg a (Expr' a)
    | ExpApp a (Expr' a) (Expr' a)
    | ExpLst a [Expr' a]
    | ExpLit a (Literal' a)
    | ExpCon a ConIdent
    | ExpVar a VarIdent
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type AddOp = AddOp' BNFC'Position
data AddOp' a = OpAdd a | OpSub a
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type MulOp = MulOp' BNFC'Position
data MulOp' a = OpMul a | OpDiv a
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type CmpOp = CmpOp' BNFC'Position
data CmpOp' a
    = OpEq a | OpNeq a | OpGrt a | OpGeq a | OpLrt a | OpLeq a
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type Match = Match' BNFC'Position
data Match' a = MatchT a (AbsPattern' a) (Expr' a)
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type AbsPattern = AbsPattern' BNFC'Position
data AbsPattern' a
    = PatAs a (Pattern' a) VarIdent | Pat a (Pattern' a)
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type Pattern = Pattern' BNFC'Position
data Pattern' a
    = PatCon a ConIdent [SubPat' a]
    | PatLL a (Pattern' a) (Pattern' a)
    | PatLst a [Pattern' a]
    | PatLit a (Literal' a)
    | PatVar a VarIdent
    | PatDef a
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

type SubPat = SubPat' BNFC'Position
data SubPat' a = SubPatT a (Pattern' a)
  deriving (C.Eq, C.Ord, C.Show, C.Read, C.Functor, C.Foldable, C.Traversable)

newtype VarIdent = VarIdent String
  deriving (C.Eq, C.Ord, C.Show, C.Read, Data.String.IsString)

newtype ConIdent = ConIdent String
  deriving (C.Eq, C.Ord, C.Show, C.Read, Data.String.IsString)

-- | Start position (line, column) of something.

type BNFC'Position = C.Maybe (C.Int, C.Int)

pattern BNFC'NoPosition :: BNFC'Position
pattern BNFC'NoPosition = C.Nothing

pattern BNFC'Position :: C.Int -> C.Int -> BNFC'Position
pattern BNFC'Position line col = C.Just (line, col)

-- | Get the start position of something.

class HasPosition a where
  hasPosition :: a -> BNFC'Position

instance HasPosition Program where
  hasPosition = \case
    ProgramT p _ -> p

instance HasPosition Literal where
  hasPosition = \case
    LitInt p _ -> p
    LitTrue p -> p
    LitFalse p -> p

instance HasPosition SimpleType where
  hasPosition = \case
    SimpleTypeT p _ _ -> p

instance HasPosition Constr where
  hasPosition = \case
    ConstrT p _ _ -> p

instance HasPosition Type where
  hasPosition = \case
    TypArr p _ _ -> p
    TypApp p _ _ _ -> p
    TypVar p _ -> p
    TypCon p _ -> p
    TypLst p _ -> p

instance HasPosition Decl where
  hasPosition = \case
    DeclData p _ _ -> p
    DeclFunc p _ _ _ -> p
    DeclFunT p _ _ -> p

instance HasPosition Expr where
  hasPosition = \case
    ExpIf p _ _ _ -> p
    ExpMth p _ _ -> p
    ExpLet p _ _ -> p
    ExpLmb p _ _ _ -> p
    ExpOr p _ _ -> p
    ExpAnd p _ _ -> p
    ExpCmp p _ _ _ -> p
    ExpAdd p _ _ _ -> p
    ExpMul p _ _ _ -> p
    ExpChn p _ _ -> p
    ExpNot p _ -> p
    ExpNeg p _ -> p
    ExpApp p _ _ -> p
    ExpLst p _ -> p
    ExpLit p _ -> p
    ExpCon p _ -> p
    ExpVar p _ -> p

instance HasPosition AddOp where
  hasPosition = \case
    OpAdd p -> p
    OpSub p -> p

instance HasPosition MulOp where
  hasPosition = \case
    OpMul p -> p
    OpDiv p -> p

instance HasPosition CmpOp where
  hasPosition = \case
    OpEq p -> p
    OpNeq p -> p
    OpGrt p -> p
    OpGeq p -> p
    OpLrt p -> p
    OpLeq p -> p

instance HasPosition Match where
  hasPosition = \case
    MatchT p _ _ -> p

instance HasPosition AbsPattern where
  hasPosition = \case
    PatAs p _ _ -> p
    Pat p _ -> p

instance HasPosition Pattern where
  hasPosition = \case
    PatCon p _ _ -> p
    PatLL p _ _ -> p
    PatLst p _ -> p
    PatLit p _ -> p
    PatVar p _ -> p
    PatDef p -> p

instance HasPosition SubPat where
  hasPosition = \case
    SubPatT p _ -> p

