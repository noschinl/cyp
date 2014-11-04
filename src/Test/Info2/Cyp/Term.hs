module Test.Info2.Cyp.Term
    ( IdxName
    , Term(..)
    , Prop(..)
    , CypFixity(..), unparseFixities -- XXX
    , collectFrees
    , defaultToFree
    , defaultToSchematic
    , generalizeExcept
    , generalizeExceptProp
    , iparseTerm
    , iparseProp
    , isFree
    , isSchematic
    , listComb
    , mApp
    , match
    , matchProp
    , stripComb
    , subst
    , substProp
    , symPropEq
    , symUMinus
    , translateExp
    , translateName
    , translatePat
    , unparseTerm
    , unparseProp
    )
where

import Control.Monad ((>=>), liftM2, when)
import Data.List (find)
import Data.Traversable (traverse)
import qualified Language.Haskell.Exts.Parser as P
import Language.Haskell.Exts.Fixity (Fixity (..), baseFixities)
import qualified Language.Haskell.Exts.Syntax as Exts
import Language.Haskell.Exts.Syntax (Assoc (..),  Boxed(..), Exp(..), Literal (..), QName (..), QOp (..), SpecialCon (..), Name (..), ModuleName (..))
import Text.PrettyPrint (parens, quotes, text, (<+>), Doc)

import Test.Info2.Cyp.Util

type IdxName = (String, Int)

data Term
    = Application Term Term
    | Const String
    | Free IdxName -- Free variable
    | Schematic IdxName -- Schematic variable
    | Literal Literal
    deriving (Show, Eq)

data Prop = Prop Term Term
    deriving (Eq, Show) -- lhs, rhs


stripComb :: Term -> (Term, [Term])
stripComb term = work (term, [])
  where work (Application f a, xs) = work (f, a : xs)
        work x = x

listComb :: Term -> [Term] -> Term
listComb = foldl Application

mApp :: Monad m => m Term -> m Term -> m Term
mApp = liftM2 Application

infixl 1 `mApp`

match :: Term -> Term -> [(IdxName, Term)] -> Maybe [(IdxName, Term)]
match (Application f a) (Application f' a') s = match f f' s >>= match a a'
match t (Schematic v) s = case lookup v s of
    Nothing -> Just $ (v,t) : s
    Just t' -> if t == t' then Just s else Nothing
match term pat s
    | term == pat = Just s
    | otherwise = Nothing

subst :: Term -> [(IdxName, Term)] -> Term
subst (Application f a) s = Application (subst f s) (subst a s)
subst (Schematic v) s = case lookup v s of
      Nothing -> Schematic v
      Just t -> t
subst t _ = t

-- Generalizes a term by turning Frees into Schematics.
-- XXX: Result may not be as general as intended, as
-- generalizing may reuse names ...
generalizeExcept :: [IdxName] -> Term -> Term
generalizeExcept vs (Application s t) = Application (generalizeExcept vs s) (generalizeExcept vs t)
generalizeExcept vs (Free v)
    | v `elem` vs = Free v
    | otherwise = Schematic v
generalizeExcept _ t = t


collectFrees :: Term -> [IdxName]-> [IdxName]
collectFrees (Application f a) xs = collectFrees f $ collectFrees a xs
collectFrees (Const _) xs = xs
collectFrees (Free v) xs = v : xs
collectFrees (Literal _) xs = xs
collectFrees (Schematic _) xs = xs

isFree :: Term -> Bool
isFree (Free _) = True
isFree _ = False

isSchematic :: Term -> Bool
isSchematic (Schematic _) = True
isSchematic _ = False

symPropEq :: String
symPropEq = ".=."

symUMinus :: String
symUMinus = "-"


{- Prop operations --------------------------------------------------}

matchProp :: Prop -> Prop -> [(IdxName, Term)] -> Maybe [(IdxName, Term)]
matchProp (Prop l r) (Prop l' r') = match l l' >=> match r r'

substProp :: Prop -> [(IdxName, Term)] -> Prop
substProp (Prop l r) s = Prop (subst l s) (subst r s)

-- Generalizes a prop by turning Frees into Schematics.
-- XXX: Result may not be as general as intended, as
-- generalizing may reuse names ...
generalizeExceptProp :: [IdxName] -> Prop -> Prop
generalizeExceptProp vs (Prop l r) = Prop (generalizeExcept vs l) (generalizeExcept vs r)


{- Parsing ----------------------------------------------------------}

iparseTermRaw :: P.ParseMode -> (String -> Err Term) -> String -> Err Term
iparseTermRaw mode f s = errCtxt (text "Parsing term" <+> quotes (text s)) $
    case P.parseExpWithMode mode s of
        P.ParseOk p -> translateExp f p
        x@(P.ParseFailed _ _) -> errStr $ show x

defaultToFree :: [String] -> String -> Err Term
defaultToFree consts x = return $ if x `elem` consts then Const x else Free (x,0) -- XXX: Consider?

defaultToSchematic :: [String] -> String -> Err Term
defaultToSchematic consts x = return $ if x `elem` consts then Const x else Schematic (x, 0) -- XXX: Consider?

checkHasPropEq :: Term -> Err ()
checkHasPropEq term = when (hasPropEq term) $
    errStr $ "A term may not include the equality symbol '" ++ symPropEq ++ "'."
  where
    hasPropEq (Application f a) = hasPropEq f || hasPropEq a
    hasPropEq (Const c) | c == symPropEq = True
    hasPropEq _ = False

iparseTerm :: (String -> Err Term)-> String -> Err Term
iparseTerm f s = do
    term <- iparseTermRaw mode f s
    checkHasPropEq term
    return term
  where mode = P.defaultParseMode { P.fixities = Just baseFixities }


iparseProp :: (String -> Err Term) -> String -> Err Prop
iparseProp f s = do
    term <- iparseTermRaw mode f' s
    (lhs, rhs) <- case term of
        Application (Application (Const c) lhs) rhs | c == symPropEq -> Right (lhs, rhs)
        _ -> errStr $ "Term '" ++ s ++ "' is not a proposition"
    checkHasPropEq lhs
    checkHasPropEq rhs
    return $ Prop lhs rhs
  where
    f' x = if x == symPropEq then return $ Const x else f x
    mode = P.defaultParseMode { P.fixities = Just $ Fixity AssocNone (-1) (UnQual $ Symbol symPropEq) : baseFixities }


{- Transform Exp to Term ---------------------------------------------}

translateExp :: (String -> Err Term) -> Exp -> Err Term
translateExp f (Var v) = f $ translateQName v
translateExp _ (Con c) = return . Const $ translateQName c
translateExp _ (Lit l) = return $ Literal l
translateExp f (InfixApp e1 op e2) =
    translateQOp f op `mApp` translateExp f e1 `mApp` translateExp f e2
translateExp f (App e1 e2) = translateExp f e1 `mApp` translateExp f e2
translateExp f (NegApp e) = return (Const symUMinus) `mApp` translateExp f e
translateExp f (LeftSection e op) = translateQOp f op `mApp` translateExp f e
translateExp f (Paren e) = translateExp f e
translateExp f (List l) = foldr (\e es -> Right (Const ":") `mApp` translateExp f e `mApp` es) (Right $ Const "[]") l
translateExp _ e = errStr $ "Unsupported expression syntax used: " ++ show e

translatePat :: Exts.Pat -> Err Term
translatePat (Exts.PVar v) = Right $ Schematic (translateName v, 0)
translatePat (Exts.PLit l) = Right $ Literal l
-- PNeg?
translatePat (Exts.PNPlusK _ _) = errStr "n+k patterns are not supported"
translatePat (Exts.PInfixApp p1 qn p2) =
    (return . Const $ translateQName qn) `mApp` translatePat p1 `mApp` translatePat p2
translatePat (Exts.PApp qn ps) = do
    cs <- traverse translatePat ps
    return $ listComb (Const $ translateQName qn) cs
translatePat (Exts.PTuple _) = errStr "tuple patterns are not supported"
translatePat (Exts.PList ps) = foldr (\p cs -> Right (Const ":") `mApp` translatePat p `mApp` cs) (Right $ Const "[]") ps
translatePat (Exts.PParen p) = translatePat p
translatePat (Exts.PAsPat _ _) = errStr "as patterns are not supported"
translatePat Exts.PWildCard = errStr "wildcard patterns are not supported"
translatePat f = errStr $ "unsupported pattern type: " ++ show f

translateQOp :: (String -> Err Term) -> QOp -> Err Term
translateQOp _ (QConOp op) = return . Const $ translateQName op
translateQOp f (QVarOp op) = f $ translateQName op

translateQName :: QName -> String
translateQName (Qual (ModuleName m) (Ident n)) = m ++ "." ++ n
translateQName (Qual (ModuleName m) (Symbol n)) = m ++ "." ++ n
translateQName (UnQual (Ident n)) = n
translateQName (UnQual (Symbol n)) = n
translateQName (Special UnitCon) = "()"
translateQName (Special ListCon) = "[]"
translateQName (Special FunCon) = "->"
translateQName (Special Cons) = ":"
translateQName (Special (TupleCon b n)) = case b of
    Boxed -> "(#" ++ replicate n ',' ++ "#)"
    Unboxed -> "(" ++ replicate n ',' ++ ")"
translateQName (Special UnboxedSingleCon) = "(# #)"

translateName :: Name -> String
translateName (Ident s) = s
translateName (Symbol s) = s



{- Pretty printing --------------------------------------------------}

data Prio = IntPrio Int | AppPrio | AtomPrio deriving (Eq, Show)
data CypFixity = CypFixity Assoc Prio String deriving Show
data CypApplied = Applied0 | Applied1 | AppliedFull deriving (Eq, Show)

instance Ord Prio where
    compare (IntPrio i) (IntPrio j) = compare i j
    compare (IntPrio _) _ = LT
    compare _ (IntPrio _) = GT
    compare AppPrio AppPrio = EQ
    compare AppPrio AtomPrio = LT
    compare AtomPrio AppPrio = GT
    compare AtomPrio AtomPrio = EQ

unparseFixities :: [CypFixity]
unparseFixities = map (\(Fixity assoc prio name) -> CypFixity assoc (IntPrio prio) $ translateQName name) baseFixities

atomFixity :: (Assoc, Prio, CypApplied)
atomFixity = (AssocNone, AtomPrio, AppliedFull)

unparseTerm :: Term -> Doc
unparseTerm = finalize . unparseTermRaw
  where
    finalize (d, (_,_, AppliedFull)) = d
    finalize (d, _) = parens d

unparseProp :: Prop -> Doc
unparseProp (Prop l r) = unparseTerm l <+> text symPropEq <+> unparseTerm r

unparseTermRaw :: Term -> (Doc, (Assoc, Prio, CypApplied))
unparseTermRaw (Application tl tr) = (doc', fixity')
  where
    l = unparseTermRaw tl
    r = applyFull $ unparseTermRaw tr

    doc' = case applied l of
        Applied0
            | prio r > prio l -> doc r <+> doc l
            | prio l == prio r && assocsTo AssocLeft l r -> (doc r) <+> (doc l)
            | otherwise -> close r <+> (doc l)
        Applied1
            | prio r > prio l -> doc l <+> doc r
            | prio l == prio r && assocsTo AssocRight l r -> doc l <+> doc r
            | otherwise -> doc l <+> close r
        AppliedFull
            | prio l < AppPrio -> close l <+> close r
            | otherwise -> doc l <+> close r

    fixity' = case applied l of
        Applied0 -> (assoc l, prio l, Applied1)
        Applied1 -> (assoc l, prio l, AppliedFull)
        AppliedFull -> (AssocLeft, AppPrio, AppliedFull)

    close u = case prio u of
        AtomPrio -> doc u
        _ -> parens (doc u)

    applyFull u = case applied u of
        AppliedFull -> u
        _ -> (parens (doc u), atomFixity)

    assocsTo a l r = prio l == prio r && assoc l == a && assoc r == a

    doc (x, _) = x
    assoc (_, (x, _, _)) = x
    prio (_, (_, x, _)) = x
    applied (_, (_, _, x)) = x
unparseTermRaw (Literal l) = (text $ unparseLiteral l, atomFixity)
unparseTermRaw (Const c) =
    case find (\(CypFixity _ _ n) -> n == c) unparseFixities of
        Nothing -> (text c, atomFixity)
        Just (CypFixity assoc prio _) -> (text c, (assoc, prio, Applied0))
unparseTermRaw (Free (v,_)) = (text v, atomFixity) -- XXX: unparse with showing index?
unparseTermRaw (Schematic (v,_)) = (text $ "?" ++ v, atomFixity) -- XXX: unparse with showing index?

unparseLiteral :: Literal -> String
unparseLiteral (Char c) = show c
unparseLiteral (String s) = show s
unparseLiteral (Int c) = show c
unparseLiteral (Frac c) = show c
unparseLiteral (PrimInt c) = show c
unparseLiteral (PrimWord c) = show c
unparseLiteral (PrimFloat c) = show c
unparseLiteral (PrimDouble c) = show c
unparseLiteral (PrimChar c) = show c
unparseLiteral (PrimString c) = show c
