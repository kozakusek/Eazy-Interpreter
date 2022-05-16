-- File generated by the BNF Converter (bnfc 2.9.4).

{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
#if __GLASGOW_HASKELL__ <= 708
{-# LANGUAGE OverlappingInstances #-}
#endif

-- | Pretty-printer for Eazy.

module Eazy.Print where

import Prelude
  ( ($), (.)
  , Bool(..), (==), (<)
  , Int, Integer, Double, (+), (-), (*)
  , String, (++)
  , ShowS, showChar, showString
  , all, elem, foldr, id, map, null, replicate, shows, span
  )
import Data.Char ( Char, isSpace )
import qualified Eazy.Abs

-- | The top-level printing method.

printTree :: Print a => a -> String
printTree = render . prt 0

type Doc = [ShowS] -> [ShowS]

doc :: ShowS -> Doc
doc = (:)

render :: Doc -> String
render d = rend 0 False (map ($ "") $ d []) ""
  where
  rend
    :: Int        -- ^ Indentation level.
    -> Bool       -- ^ Pending indentation to be output before next character?
    -> [String]
    -> ShowS
  rend i p = \case
      "["      :ts -> char '[' . rend i False ts
      "("      :ts -> char '(' . rend i False ts
      "{"      :ts -> onNewLine i     p . showChar   '{'  . new (i+1) ts
      "}" : ";":ts -> onNewLine (i-1) p . showString "};" . new (i-1) ts
      "}"      :ts -> onNewLine (i-1) p . showChar   '}'  . new (i-1) ts
      [";"]        -> char ';'
      ";"      :ts -> char ';' . new i ts
      t  : ts@(s:_) | closingOrPunctuation s
                   -> pending . showString t . rend i False ts
      t        :ts -> pending . space t      . rend i False ts
      []           -> id
    where
    -- Output character after pending indentation.
    char :: Char -> ShowS
    char c = pending . showChar c

    -- Output pending indentation.
    pending :: ShowS
    pending = if p then indent i else id

  -- Indentation (spaces) for given indentation level.
  indent :: Int -> ShowS
  indent i = replicateS (2*i) (showChar ' ')

  -- Continue rendering in new line with new indentation.
  new :: Int -> [String] -> ShowS
  new j ts = showChar '\n' . rend j True ts

  -- Make sure we are on a fresh line.
  onNewLine :: Int -> Bool -> ShowS
  onNewLine i p = (if p then id else showChar '\n') . indent i

  -- Separate given string from following text by a space (if needed).
  space :: String -> ShowS
  space t s =
    case (all isSpace t', null spc, null rest) of
      (True , _   , True ) -> []              -- remove trailing space
      (False, _   , True ) -> t'              -- remove trailing space
      (False, True, False) -> t' ++ ' ' : s   -- add space if none
      _                    -> t' ++ s
    where
      t'          = showString t []
      (spc, rest) = span isSpace s

  closingOrPunctuation :: String -> Bool
  closingOrPunctuation [c] = c `elem` closerOrPunct
  closingOrPunctuation _   = False

  closerOrPunct :: String
  closerOrPunct = ")],;"

parenth :: Doc -> Doc
parenth ss = doc (showChar '(') . ss . doc (showChar ')')

concatS :: [ShowS] -> ShowS
concatS = foldr (.) id

concatD :: [Doc] -> Doc
concatD = foldr (.) id

replicateS :: Int -> ShowS -> ShowS
replicateS n f = concatS (replicate n f)

-- | The printer class does the job.

class Print a where
  prt :: Int -> a -> Doc

instance {-# OVERLAPPABLE #-} Print a => Print [a] where
  prt i = concatD . map (prt i)

instance Print Char where
  prt _ c = doc (showChar '\'' . mkEsc '\'' c . showChar '\'')

instance Print String where
  prt _ = printString

printString :: String -> Doc
printString s = doc (showChar '"' . concatS (map (mkEsc '"') s) . showChar '"')

mkEsc :: Char -> Char -> ShowS
mkEsc q = \case
  s | s == q -> showChar '\\' . showChar s
  '\\' -> showString "\\\\"
  '\n' -> showString "\\n"
  '\t' -> showString "\\t"
  s -> showChar s

prPrec :: Int -> Int -> Doc -> Doc
prPrec i j = if j < i then parenth else id

instance Print Integer where
  prt _ x = doc (shows x)

instance Print Double where
  prt _ x = doc (shows x)

instance Print Eazy.Abs.VarIdent where
  prt _ (Eazy.Abs.VarIdent i) = doc $ showString i
instance Print Eazy.Abs.ConIdent where
  prt _ (Eazy.Abs.ConIdent i) = doc $ showString i
instance Print (Eazy.Abs.Program' a) where
  prt i = \case
    Eazy.Abs.ProgramT _ decls -> prPrec i 0 (concatD [prt 0 decls])

instance Print [Eazy.Abs.VarIdent] where
  prt _ [] = concatD []
  prt _ (x:xs) = concatD [prt 0 x, prt 0 xs]

instance Print (Eazy.Abs.Literal' a) where
  prt i = \case
    Eazy.Abs.LitInt _ n -> prPrec i 0 (concatD [prt 0 n])
    Eazy.Abs.LitTrue _ -> prPrec i 0 (concatD [doc (showString "True")])
    Eazy.Abs.LitFalse _ -> prPrec i 0 (concatD [doc (showString "False")])

instance Print (Eazy.Abs.SimpleType' a) where
  prt i = \case
    Eazy.Abs.SimpleTypeT _ conident varidents -> prPrec i 0 (concatD [prt 0 conident, prt 0 varidents])

instance Print (Eazy.Abs.Constr' a) where
  prt i = \case
    Eazy.Abs.ConstrT _ conident types -> prPrec i 0 (concatD [prt 0 conident, prt 2 types])

instance Print (Eazy.Abs.Type' a) where
  prt i = \case
    Eazy.Abs.TypArr _ type_1 type_2 -> prPrec i 0 (concatD [prt 1 type_1, doc (showString "->"), prt 0 type_2])
    Eazy.Abs.TypApp _ conident type_ types -> prPrec i 1 (concatD [prt 0 conident, prt 2 type_, prt 2 types])
    Eazy.Abs.TypVar _ varident -> prPrec i 2 (concatD [prt 0 varident])
    Eazy.Abs.TypCon _ conident -> prPrec i 2 (concatD [prt 0 conident])
    Eazy.Abs.TypLst _ type_ -> prPrec i 2 (concatD [doc (showString "["), prt 0 type_, doc (showString "]")])

instance Print [Eazy.Abs.Constr' a] where
  prt _ [] = concatD []
  prt _ [x] = concatD [prt 0 x]
  prt _ (x:xs) = concatD [prt 0 x, doc (showString "|"), prt 0 xs]

instance Print [Eazy.Abs.Type' a] where
  prt _ [] = concatD []
  prt _ (x:xs) = concatD [prt 2 x, prt 2 xs]

instance Print (Eazy.Abs.Decl' a) where
  prt i = \case
    Eazy.Abs.DeclData _ simpletype constrs -> prPrec i 0 (concatD [doc (showString "type"), prt 0 simpletype, doc (showString "="), prt 0 constrs])
    Eazy.Abs.DeclFunc _ varident varidents expr -> prPrec i 0 (concatD [prt 0 varident, prt 0 varidents, doc (showString "="), prt 0 expr])
    Eazy.Abs.DeclFunT _ varident type_ -> prPrec i 0 (concatD [prt 0 varident, doc (showString ":"), prt 0 type_])

instance Print [Eazy.Abs.Decl' a] where
  prt _ [] = concatD []
  prt _ [x] = concatD [prt 0 x]
  prt _ (x:xs) = concatD [prt 0 x, doc (showString ";"), prt 0 xs]

instance Print (Eazy.Abs.Expr' a) where
  prt i = \case
    Eazy.Abs.ExpIf _ expr1 expr2 expr3 -> prPrec i 0 (concatD [prt 3 expr1, doc (showString "if"), prt 0 expr2, doc (showString "otherwise"), prt 0 expr3])
    Eazy.Abs.ExpMth _ expr matchs -> prPrec i 0 (concatD [doc (showString "match"), prt 0 expr, doc (showString "with"), doc (showString "{"), prt 0 matchs, doc (showString "}")])
    Eazy.Abs.ExpLet _ decls expr -> prPrec i 0 (concatD [doc (showString "let"), doc (showString "{"), prt 0 decls, doc (showString "}"), doc (showString "in"), prt 0 expr])
    Eazy.Abs.ExpLmb _ type_ varidents expr -> prPrec i 0 (concatD [doc (showString "lambda"), doc (showString "{"), prt 0 type_, doc (showString "}"), prt 0 varidents, doc (showString "->"), prt 0 expr])
    Eazy.Abs.ExpOr _ expr1 expr2 -> prPrec i 0 (concatD [prt 1 expr1, doc (showString "||"), prt 0 expr2])
    Eazy.Abs.ExpAnd _ expr1 expr2 -> prPrec i 1 (concatD [prt 2 expr1, doc (showString "&&"), prt 1 expr2])
    Eazy.Abs.ExpCmp _ expr1 cmpop expr2 -> prPrec i 2 (concatD [prt 2 expr1, prt 0 cmpop, prt 3 expr2])
    Eazy.Abs.ExpEqs _ expr1 eqsop expr2 -> prPrec i 2 (concatD [prt 2 expr1, prt 0 eqsop, prt 3 expr2])
    Eazy.Abs.ExpAdd _ expr1 addop expr2 -> prPrec i 3 (concatD [prt 3 expr1, prt 0 addop, prt 4 expr2])
    Eazy.Abs.ExpMul _ expr1 mulop expr2 -> prPrec i 4 (concatD [prt 4 expr1, prt 0 mulop, prt 5 expr2])
    Eazy.Abs.ExpChn _ expr1 expr2 -> prPrec i 5 (concatD [prt 6 expr1, doc (showString "::"), prt 5 expr2])
    Eazy.Abs.ExpNot _ expr -> prPrec i 6 (concatD [doc (showString "~"), prt 7 expr])
    Eazy.Abs.ExpNeg _ expr -> prPrec i 6 (concatD [doc (showString "-"), prt 7 expr])
    Eazy.Abs.ExpApp _ expr1 expr2 -> prPrec i 7 (concatD [prt 7 expr1, prt 8 expr2])
    Eazy.Abs.ExpLst _ exprs -> prPrec i 8 (concatD [doc (showString "["), prt 0 exprs, doc (showString "]")])
    Eazy.Abs.ExpLit _ literal -> prPrec i 8 (concatD [prt 0 literal])
    Eazy.Abs.ExpCon _ conident -> prPrec i 8 (concatD [prt 0 conident])
    Eazy.Abs.ExpVar _ varident -> prPrec i 8 (concatD [prt 0 varident])

instance Print [Eazy.Abs.Expr' a] where
  prt _ [] = concatD []
  prt _ [x] = concatD [prt 0 x]
  prt _ (x:xs) = concatD [prt 0 x, doc (showString ","), prt 0 xs]

instance Print (Eazy.Abs.AddOp' a) where
  prt i = \case
    Eazy.Abs.OpAdd _ -> prPrec i 0 (concatD [doc (showString "+")])
    Eazy.Abs.OpSub _ -> prPrec i 0 (concatD [doc (showString "-")])

instance Print (Eazy.Abs.MulOp' a) where
  prt i = \case
    Eazy.Abs.OpMul _ -> prPrec i 0 (concatD [doc (showString "*")])
    Eazy.Abs.OpDiv _ -> prPrec i 0 (concatD [doc (showString "/")])

instance Print (Eazy.Abs.EqsOp' a) where
  prt i = \case
    Eazy.Abs.OpEq _ -> prPrec i 0 (concatD [doc (showString "==")])
    Eazy.Abs.OpNeq _ -> prPrec i 0 (concatD [doc (showString "=/=")])

instance Print (Eazy.Abs.CmpOp' a) where
  prt i = \case
    Eazy.Abs.OpGrt _ -> prPrec i 0 (concatD [doc (showString ">")])
    Eazy.Abs.OpGeq _ -> prPrec i 0 (concatD [doc (showString ">=")])
    Eazy.Abs.OpLrt _ -> prPrec i 0 (concatD [doc (showString "<")])
    Eazy.Abs.OpLeq _ -> prPrec i 0 (concatD [doc (showString "<=")])

instance Print (Eazy.Abs.Match' a) where
  prt i = \case
    Eazy.Abs.MatchT _ abspattern expr -> prPrec i 0 (concatD [prt 0 abspattern, doc (showString "->"), prt 0 expr])

instance Print (Eazy.Abs.AbsPattern' a) where
  prt i = \case
    Eazy.Abs.PatAs _ pattern_ varident -> prPrec i 0 (concatD [prt 0 pattern_, doc (showString "as"), prt 0 varident])
    Eazy.Abs.Pat _ pattern_ -> prPrec i 0 (concatD [prt 0 pattern_])

instance Print (Eazy.Abs.Pattern' a) where
  prt i = \case
    Eazy.Abs.PatCon _ conident subpats -> prPrec i 0 (concatD [prt 0 conident, prt 0 subpats])
    Eazy.Abs.PatLL _ pattern_1 pattern_2 -> prPrec i 1 (concatD [prt 2 pattern_1, doc (showString "::"), prt 1 pattern_2])
    Eazy.Abs.PatLst _ patterns -> prPrec i 2 (concatD [doc (showString "["), prt 0 patterns, doc (showString "]")])
    Eazy.Abs.PatLit _ literal -> prPrec i 2 (concatD [prt 0 literal])
    Eazy.Abs.PatVar _ varident -> prPrec i 2 (concatD [prt 0 varident])
    Eazy.Abs.PatDef _ -> prPrec i 2 (concatD [doc (showString "_")])

instance Print (Eazy.Abs.SubPat' a) where
  prt i = \case
    Eazy.Abs.SubPatT _ pattern_ -> prPrec i 0 (concatD [prt 2 pattern_])

instance Print [Eazy.Abs.Match' a] where
  prt _ [] = concatD []
  prt _ [x] = concatD [prt 0 x, doc (showString ";")]
  prt _ (x:xs) = concatD [prt 0 x, doc (showString ";"), prt 0 xs]

instance Print [Eazy.Abs.Pattern' a] where
  prt _ [] = concatD []
  prt _ [x] = concatD [prt 0 x]
  prt _ (x:xs) = concatD [prt 0 x, doc (showString ","), prt 0 xs]

instance Print [Eazy.Abs.SubPat' a] where
  prt _ [] = concatD []
  prt _ (x:xs) = concatD [prt 0 x, prt 0 xs]
