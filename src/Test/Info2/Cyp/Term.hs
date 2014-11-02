module Test.Info2.Cyp.Term
    ( Term(..)
    , Prop(..)
    , CypFixity(..), unparseFixities -- XXX
    , collectFrees
    , generalizeExcept
    , generalizeExceptProp
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
    , unparseTerm
    , unparseProp
    )
where

import Control.Monad ((>=>), liftM2)
import Data.List (find)
import Language.Haskell.Exts.Fixity (Fixity (..), baseFixities)
import Language.Haskell.Exts.Syntax (Literal (..), QName(..), SpecialCon (..), Name (..), ModuleName (..), Assoc (..),  Boxed(..))
import Text.PrettyPrint (parens, text, (<+>), Doc)

data Term
    = Application Term Term
    | Const String
    | Free String -- Free variable
    | Schematic String -- Schematic variable
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

match :: Term -> Term -> [(String, Term)] -> Maybe [(String, Term)]
match (Application f a) (Application f' a') s = match f f' s >>= match a a'
match t (Schematic v) s = case lookup v s of
    Nothing -> Just $ (v,t) : s
    Just t' -> if t == t' then Just s else Nothing
match term pat s
    | term == pat = Just s
    | otherwise = Nothing

subst :: Term -> [(String, Term)] -> Term
subst (Application f a) s = Application (subst f s) (subst a s)
subst (Schematic v) s = case lookup v s of
      Nothing -> Schematic v
      Just t -> t
subst t _ = t

-- Generalizes a term by turning Frees into Schematics.
-- XXX: Result may not be as general as intended, as
-- generalizing may reuse names ...
generalizeExcept :: [String] -> Term -> Term
generalizeExcept vs (Application s t) = Application (generalizeExcept vs s) (generalizeExcept vs t)
generalizeExcept vs (Free v)
    | v `elem` vs = Free v
    | otherwise = Schematic v
generalizeExcept _ t = t


collectFrees :: Term -> [String]-> [String]
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

matchProp :: Prop -> Prop -> [(String, Term)] -> Maybe [(String, Term)]
matchProp (Prop l r) (Prop l' r') = match l l' >=> match r r'

substProp :: Prop -> [(String, Term)] -> Prop
substProp (Prop l r) s = Prop (subst l s) (subst r s)

-- Generalizes a prop by turning Frees into Schematics.
-- XXX: Result may not be as general as intended, as
-- generalizing may reuse names ...
generalizeExceptProp :: [String] -> Prop -> Prop
generalizeExceptProp vs (Prop l r) = Prop (generalizeExcept vs l) (generalizeExcept vs r)

{-- Pretty Printing --}

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
unparseFixities = map (\(Fixity assoc prio name) -> CypFixity assoc (IntPrio prio) $ trans name) baseFixities
  where
    trans (Qual (ModuleName m) (Ident n)) = m ++ "." ++ n
    trans (Qual (ModuleName m) (Symbol n)) = m ++ "." ++ n
    trans (UnQual (Ident n)) = n
    trans (UnQual (Symbol n)) = n
    trans (Special UnitCon) = "()"
    trans (Special ListCon) = "[]"
    trans (Special FunCon) = "->"
    trans (Special Cons) = ":"
    trans (Special (TupleCon b n)) = case b of
        Boxed -> "(#" ++ replicate n ',' ++ "#)"
        Unboxed -> "(" ++ replicate n ',' ++ ")"
    trans (Special UnboxedSingleCon) = "(# #)"

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
unparseTermRaw (Free v) = (text v, atomFixity)
unparseTermRaw (Schematic v) = (text $ "?" ++ v, atomFixity)

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
