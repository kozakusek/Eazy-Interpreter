module Prologue (enrich) where
import Eazy.Abs
import Eazy.ErrM (Err)

enrich :: Program -> Err Program
enrich (ProgramT x d) = return $ ProgramT x (firstPrologue ++ d)

firstPrologue :: [Decl' (Maybe (Int, Int))]
firstPrologue = [
    -- Data Types

    -- Maybe
    DeclData (Just (0, 0)) (SimpleTypeT (Just (0, 0)) (ConIdent "Maybe") [VarIdent "a"]) [
        ConstrT (Just (0, 0)) (ConIdent "Nothing") [],
        ConstrT (Just (0, 0)) (ConIdent "Just") [TypVar (Just (0, 0)) (VarIdent "a")]
    ],
    -- Either
    DeclData (Just (0, 0)) (SimpleTypeT (Just (0, 0)) (ConIdent "Either") [VarIdent "a",VarIdent "b"]) [
        ConstrT (Just (0, 0)) (ConIdent "Left") [TypVar (Just (0, 0)) (VarIdent "a")],
        ConstrT (Just (0, 0)) (ConIdent "Right") [TypVar (Just (0, 0)) (VarIdent "b")]
    ],
    -- Functions

    -- head
    DeclFunT (Just (0, 0)) (VarIdent "head") (TypArr (Just (0, 0)) 
        (TypLst (Just (0, 0)) (TypVar (Just (0, 0)) (VarIdent "a"))) 
        (TypVar (Just (0, 0)) (VarIdent "a"))
    ),
    DeclFunc (Just (0, 0)) (VarIdent "head") [VarIdent "lst"] 
        (ExpMth (Just (0, 0)) (ExpVar (Just (0, 0)) (VarIdent "lst")) [
            MatchT (Just (0, 0)) (Pat (Just (0, 0)) (PatLL (Just (0, 0)) (PatVar (Just (0, 0)) (VarIdent "x")) (PatVar (Just (0, 0)) (VarIdent "xs")))) (ExpVar (Just (0, 0)) (VarIdent "x"))
        ]
    ),

    -- tail
    DeclFunT (Just (0, 0)) (VarIdent "tail") (TypArr (Just (0, 0)) 
        (TypLst (Just (0, 0)) (TypVar (Just (0, 0)) (VarIdent "a"))) 
        (TypLst (Just (0, 0)) (TypVar (Just (0, 0)) (VarIdent "a")))
    ),
    DeclFunc (Just (0, 0)) (VarIdent "tail") [VarIdent "lst"] 
        (ExpMth (Just (0, 0)) (ExpVar (Just (0, 0)) (VarIdent "lst")) [
            MatchT (Just (0, 0)) (Pat (Just (0, 0)) (PatLL (Just (0, 0)) (PatVar (Just (0, 0)) (VarIdent "x")) (PatVar (Just (0, 0)) (VarIdent "xs")))) (ExpVar (Just (0, 0)) (VarIdent "xs"))
        ]
    ),

    -- foldl
    DeclFunT (Just (0, 0)) (VarIdent "foldl") (TypArr (Just (0, 0)) 
        (TypArr (Just (0, 0)) 
            (TypVar (Just (0, 0)) (VarIdent "a")) 
            (TypArr (Just (0, 0)) 
                (TypVar (Just (0, 0)) (VarIdent "b")) 
                (TypVar (Just (0, 0)) (VarIdent "a"))
            )
        ) 
        (TypArr (Just (0, 0)) 
            (TypVar (Just (0, 0)) (VarIdent "a")) 
            (TypArr (Just (0, 0)) 
                (TypLst (Just (0, 0)) (TypVar (Just (0, 0)) (VarIdent "b"))) 
                (TypVar (Just (0, 0)) (VarIdent "a"))
            )
        )
    ),
    DeclFunc (Just (0, 0)) (VarIdent "foldl") [VarIdent "f",VarIdent "acc",VarIdent "lst"] 
        (ExpMth (Just (0, 0)) (ExpVar (Just (0, 0)) (VarIdent "lst")) [
            MatchT (Just (0, 0)) (Pat (Just (0, 0)) (PatLL (Just (0, 0)) (PatVar (Just (0, 0)) (VarIdent "x")) (PatVar (Just (0, 0)) (VarIdent "xs")))) (ExpApp (Just (0, 0)) (ExpApp (Just (0, 0)) (ExpApp (Just (0, 0)) (ExpVar (Just (0, 0)) (VarIdent "foldl")) (ExpVar (Just (0, 0)) (VarIdent "f"))) (ExpApp (Just (0, 0)) (ExpApp (Just (0, 0)) (ExpVar (Just (0, 0)) (VarIdent "f")) (ExpVar (Just (0, 0)) (VarIdent "acc"))) (ExpVar (Just (0, 0)) (VarIdent "x")))) (ExpVar (Just (0, 0)) (VarIdent "xs"))),
            MatchT (Just (0, 0)) (Pat (Just (0, 0)) (PatLst (Just (0, 0)) [])) (ExpVar (Just (0, 0)) (VarIdent "acc"))
        ]
    ),

    -- foldr
    DeclFunT (Just (0, 0)) (VarIdent "foldr") (TypArr (Just (0, 0)) 
        (TypArr (Just (0, 0)) 
            (TypVar (Just (0, 0)) (VarIdent "a")) 
            (TypArr (Just (0, 0)) 
                (TypVar (Just (0, 0)) (VarIdent "b")) 
                (TypVar (Just (0, 0)) (VarIdent "b"))
            )
        ) 
        (TypArr (Just (0, 0)) 
            (TypVar (Just (0, 0)) (VarIdent "b")) 
            (TypArr (Just (0, 0)) 
                (TypLst (Just (0, 0)) (TypVar (Just (0, 0)) (VarIdent "a"))) 
                (TypVar (Just (0, 0)) (VarIdent "b"))
            )
        )
    ),
    DeclFunc (Just (0, 0)) (VarIdent "foldr") [VarIdent "f",VarIdent "acc",VarIdent "lst"] 
        (ExpMth (Just (0, 0)) (ExpVar (Just (0, 0)) (VarIdent "lst")) [
            MatchT (Just (0, 0)) (Pat (Just (0, 0)) (PatLL (Just (0, 0)) (PatVar (Just (0, 0)) (VarIdent "x")) (PatVar (Just (0, 0)) (VarIdent "xs")))) (ExpApp (Just (0, 0)) (ExpApp (Just (0, 0)) (ExpVar (Just (0, 0)) (VarIdent "f")) (ExpVar (Just (0, 0)) (VarIdent "x"))) (ExpApp (Just (0, 0)) (ExpApp (Just (0, 0)) (ExpApp (Just (0, 0)) (ExpVar (Just (0, 0)) (VarIdent "foldr")) (ExpVar (Just (0, 0)) (VarIdent "f"))) (ExpVar (Just (0, 0)) (VarIdent "acc"))) (ExpVar (Just (0, 0)) (VarIdent "xs")))),
            MatchT (Just (0, 0)) (Pat (Just (0, 0)) (PatLst (Just (0, 0)) [])) (ExpVar (Just (0, 0)) (VarIdent "acc"))
        ]
    ),

    -- all
    DeclFunT (Just (0, 0)) (VarIdent "all") (TypArr (Just (0, 0)) 
        (TypArr (Just (0, 0)) 
            (TypVar (Just (0, 0)) (VarIdent "a")) 
            (TypCon (Just (0, 0)) (ConIdent "Bool"))
        ) 
        (TypArr (Just (0, 0)) 
            (TypLst (Just (0, 0)) (TypVar (Just (0, 0)) (VarIdent "a"))) 
            (TypCon (Just (0, 0)) (ConIdent "Bool"))
        )
    ),
    DeclFunc (Just (0, 0)) (VarIdent "all") [VarIdent "p",VarIdent "lst"] 
        (ExpMth (Just (0, 0)) (ExpVar (Just (0, 0)) (VarIdent "lst")) [
            MatchT (Just (0, 0)) (Pat (Just (0, 0)) (PatLL (Just (0, 0)) (PatVar (Just (0, 0)) (VarIdent "x")) (PatVar (Just (0, 0)) (VarIdent "xs")))) (ExpAnd (Just (0, 0)) (ExpApp (Just (0, 0)) (ExpVar (Just (0, 0)) (VarIdent "p")) (ExpVar (Just (0, 0)) (VarIdent "x"))) (ExpApp (Just (0, 0)) (ExpApp (Just (0, 0)) (ExpVar (Just (0, 0)) (VarIdent "all")) (ExpVar (Just (0, 0)) (VarIdent "p"))) (ExpVar (Just (0, 0)) (VarIdent "xs")))),
            MatchT (Just (0, 0)) (Pat (Just (0, 0)) (PatLst (Just (0, 0)) [])) (ExpLit (Just (0, 0)) (LitTrue (Just (0, 0))))
        ]
    ),

    -- null
    DeclFunT (Just (0, 0)) (VarIdent "null") (TypArr (Just (0, 0)) 
        (TypLst (Just (0, 0)) (TypVar (Just (0, 0)) (VarIdent "a"))) 
        (TypCon (Just (0, 0)) (ConIdent "Bool"))
    ),
    DeclFunc (Just (0, 0)) (VarIdent "null") [VarIdent "lst"] 
        (ExpMth (Just (0, 0)) (ExpVar (Just (0, 0)) (VarIdent "lst")) [
            MatchT (Just (0, 0)) (Pat (Just (0, 0)) (PatLst (Just (0, 0)) [])) (ExpLit (Just (0, 0)) (LitTrue (Just (0, 0)))),MatchT (Just (0, 0)) (Pat (Just (0, 0)) (PatDef (Just (0, 0)))) (ExpLit (Just (0, 0)) (LitFalse (Just (0, 0))))
        ]
    ),

    -- last
    DeclFunT (Just (0, 0)) (VarIdent "last") (TypArr (Just (0, 0)) 
        (TypLst (Just (0, 0)) (TypVar (Just (0, 0)) (VarIdent "a"))) 
        (TypVar (Just (0, 0)) (VarIdent "a"))
    ),
    DeclFunc (Just (0, 0)) (VarIdent "last") [VarIdent "lst"] 
        (ExpMth (Just (0, 0)) (ExpVar (Just (0, 0)) (VarIdent "lst")) [
            MatchT (Just (0, 0)) (Pat (Just (0, 0)) (PatLL (Just (0, 0)) (PatVar (Just (0, 0)) (VarIdent "x")) (PatLst (Just (0, 0)) []))) (ExpVar (Just (0, 0)) (VarIdent "x")),
            MatchT (Just (0, 0)) (Pat (Just (0, 0)) (PatLL (Just (0, 0)) (PatVar (Just (0, 0)) (VarIdent "x")) (PatVar (Just (0, 0)) (VarIdent "xs")))) (ExpApp (Just (0, 0)) (ExpVar (Just (0, 0)) (VarIdent "last")) (ExpVar (Just (0, 0)) (VarIdent "xs")))
        ]
    ),

    -- find
    DeclFunT (Just (0, 0)) (VarIdent "find") (TypArr (Just (0, 0)) 
        (TypArr (Just (0, 0)) 
            (TypVar (Just (0, 0)) (VarIdent "a")) 
            (TypCon (Just (0, 0)) (ConIdent "Bool"))
        ) 
        (TypArr (Just (0, 0)) 
            (TypLst (Just (0, 0)) (TypVar (Just (0, 0)) (VarIdent "a"))) 
            (TypApp (Just (0, 0)) (ConIdent "Maybe") (TypVar (Just (0, 0)) (VarIdent "a")) [])
        )
    ),
    DeclFunc (Just (0, 0)) (VarIdent "find") [VarIdent "p",VarIdent "lst"] 
        (ExpMth (Just (0, 0)) (ExpVar (Just (0, 0)) (VarIdent "lst")) [
            MatchT (Just (0, 0)) (Pat (Just (0, 0)) (PatLL (Just (0, 0)) (PatVar (Just (0, 0)) (VarIdent "x")) (PatVar (Just (0, 0)) (VarIdent "xs")))) (ExpIf (Just (0, 0)) (ExpApp (Just (0, 0)) (ExpCon (Just (0, 0)) (ConIdent "Just")) (ExpVar (Just (0, 0)) (VarIdent "x"))) (ExpApp (Just (0, 0)) (ExpVar (Just (0, 0)) (VarIdent "p")) (ExpVar (Just (0, 0)) (VarIdent "x"))) (ExpApp (Just (0, 0)) (ExpApp (Just (0, 0)) (ExpVar (Just (0, 0)) (VarIdent "find")) (ExpVar (Just (0, 0)) (VarIdent "p"))) (ExpVar (Just (0, 0)) (VarIdent "xs")))),
            MatchT (Just (0, 0)) (Pat (Just (0, 0)) (PatLst (Just (0, 0)) [])) (ExpCon (Just (0, 0)) (ConIdent "Nothing"))
        ]
    ),

    -- reverse
    DeclFunT (Just (0, 0)) (VarIdent "reverse") (TypArr (Just (0, 0)) 
        (TypLst (Just (0, 0)) (TypVar (Just (0, 0)) (VarIdent "a"))) 
        (TypLst (Just (0, 0)) (TypVar (Just (0, 0)) (VarIdent "a")))
    ),
    DeclFunc (Just (0, 0)) (VarIdent "reverse") [VarIdent "lst"] 
        (ExpMth (Just (0, 0)) (ExpVar (Just (0, 0)) (VarIdent "lst")) [
            MatchT (Just (0, 0)) (Pat (Just (0, 0)) (PatLL (Just (0, 0)) (PatVar (Just (0, 0)) (VarIdent "x")) (PatVar (Just (0, 0)) (VarIdent "xs")))) (ExpChn (Just (0, 0)) (ExpApp (Just (0, 0)) (ExpVar (Just (0, 0)) (VarIdent "reverse")) (ExpVar (Just (0, 0)) (VarIdent "xs"))) (ExpLst (Just (0, 0)) [ExpVar (Just (0, 0)) (VarIdent "x")])),
            MatchT (Just (0, 0)) (Pat (Just (0, 0)) (PatLst (Just (0, 0)) [])) (ExpLst (Just (0, 0)) [])
        ]
    ),

    -- and
    DeclFunT (Just (0, 0)) (VarIdent "and") (TypArr (Just (0, 0)) 
        (TypLst (Just (0, 0)) (TypCon (Just (0, 0)) (ConIdent "Bool"))) 
        (TypCon (Just (0, 0)) (ConIdent "Bool"))
    ),
    DeclFunc (Just (0, 0)) (VarIdent "and") [VarIdent "lst"] 
        (ExpMth (Just (0, 0)) (ExpVar (Just (0, 0)) (VarIdent "lst")) [
            MatchT (Just (0, 0)) (Pat (Just (0, 0)) (PatLL (Just (0, 0)) (PatVar (Just (0, 0)) (VarIdent "x")) (PatVar (Just (0, 0)) (VarIdent "xs")))) (ExpAnd (Just (0, 0)) (ExpVar (Just (0, 0)) (VarIdent "x")) (ExpApp (Just (0, 0)) (ExpVar (Just (0, 0)) (VarIdent "and")) (ExpVar (Just (0, 0)) (VarIdent "xs")))),
            MatchT (Just (0, 0)) (Pat (Just (0, 0)) (PatLst (Just (0, 0)) [])) (ExpLit (Just (0, 0)) (LitTrue (Just (0, 0))))
        ]
    ),

    -- or
    DeclFunT (Just (0, 0)) (VarIdent "or") (TypArr (Just (0, 0)) 
        (TypLst (Just (0, 0)) (TypCon (Just (0, 0)) (ConIdent "Bool"))) 
        (TypCon (Just (0, 0)) (ConIdent "Bool"))
    ),
    DeclFunc (Just (0, 0)) (VarIdent "or") [VarIdent "lst"] 
        (ExpMth (Just (0, 0)) (ExpVar (Just (0, 0)) (VarIdent "lst")) [
            MatchT (Just (0, 0)) (Pat (Just (0, 0)) (PatLL (Just (0, 0)) (PatVar (Just (0, 0)) (VarIdent "x")) (PatVar (Just (0, 0)) (VarIdent "xs")))) (ExpOr (Just (0, 0)) (ExpVar (Just (0, 0)) (VarIdent "x")) (ExpApp (Just (0, 0)) (ExpVar (Just (0, 0)) (VarIdent "or")) (ExpVar (Just (0, 0)) (VarIdent "xs")))),
            MatchT (Just (0, 0)) (Pat (Just (0, 0)) (PatLst (Just (0, 0)) [])) (ExpLit (Just (0, 0)) (LitFalse (Just (0, 0))))
        ]
    ),
    
    DeclFunT (Just (0, 0)) (VarIdent "map") (TypArr (Just (0, 0)) 
        (TypArr (Just (0, 0)) 
            (TypVar (Just (0, 0)) (VarIdent "a")) 
            (TypVar (Just (0, 0)) (VarIdent "b"))
        ) 
        (TypArr (Just (0, 0)) 
            (TypLst (Just (0, 0)) (TypVar (Just (0, 0)) (VarIdent "a"))) 
            (TypLst (Just (0, 0)) (TypVar (Just (0, 0)) (VarIdent "b")))
        )
    ),
    DeclFunc (Just (0, 0)) (VarIdent "map") [VarIdent "f",VarIdent "lst"] 
        (ExpMth (Just (0, 0)) (ExpVar (Just (0, 0)) (VarIdent "lst")) [
            MatchT (Just (0, 0)) (Pat (Just (0, 0)) (PatLL (Just (0, 0)) (PatVar (Just (0, 0)) (VarIdent "x")) (PatVar (Just (0, 0)) (VarIdent "xs")))) (ExpChn (Just (0, 0)) (ExpApp (Just (0, 0)) (ExpVar (Just (0, 0)) (VarIdent "f")) (ExpVar (Just (0, 0)) (VarIdent "x"))) (ExpApp (Just (0, 0)) (ExpApp (Just (0, 0)) (ExpVar (Just (0, 0)) (VarIdent "map")) (ExpVar (Just (0, 0)) (VarIdent "f"))) (ExpVar (Just (0, 0)) (VarIdent "xs")))),
            MatchT (Just (0, 0)) (Pat (Just (0, 0)) (PatLst (Just (0, 0)) [])) (ExpLst (Just (0, 0)) [])
        ]
    )
    ]
