{-# LANGUAGE FlexibleInstances #-}
module Test.Info2.Cyp.Parser
    ( ParseLemma (..)
    , ParseCase (..)
    , ParseCompCase (..)
    , ParseCaseBody (..)
    , ParseProof (..)
    , cthyParser
    , cprfParser
    , readAxiom
    , readDataType
    , readFunc
    , readGoal
    , readSym
    )
where

import Control.Monad (void)
import Data.Char
import Data.Maybe
import Text.Parsec as Parsec
import qualified Language.Haskell.Exts.Parser as P
import qualified Language.Haskell.Exts.Syntax as Exts
import Language.Haskell.Exts.SrcLoc (SrcSpanInfo)
import Text.PrettyPrint (quotes, text, (<+>), Doc)
import Text.Read (readEither)

import Test.Info2.Cyp.Env
import Test.Info2.Cyp.Term
import Test.Info2.Cyp.Types
import Test.Info2.Cyp.Util

data ParseDeclTree
    = DataDecl String
    | SymDecl String
    | Axiom String String
    | FunDef String
    | Goal String
    deriving Show

data ParseLemma = ParseLemma String RawProp ParseProof -- ^ Proposition, Proof

data ParseCaseBody = ParseCaseBody
    { pcbToShow :: Maybe RawProp
    , pcbAssms :: [Named RawProp]
    , pcbProof :: ParseProof
    }

data ParseCase = ParseCase
    { pcCons :: RawTerm
    , pcBody :: ParseCaseBody
    }

data ParseCompCase = ParseCompCase
    { pccCaseNum :: Int
    , pccBody :: ParseCaseBody
    }

data ParseProof
    = ParseInduction String RawTerm [ParseCase] -- ^ data type, induction variable, cases
    | ParseCompInduction String [String] [ParseCompCase] -- ^ function, induction variables, cases
    | ParseEquation (EqnSeqq RawTerm)
    | ParseExt RawTerm RawProp ParseProof -- ^ fixed variable, to show, subproof
    | ParseCases String RawTerm [ParseCase] -- ^ data type, term, cases
    | ParseCheating


trim :: String -> String
trim = reverse . dropWhile isSpace . reverse . dropWhile isSpace

toParsec :: (a -> String) -> Either a b -> Parsec c u b
toParsec f = either (fail . f) return


{- Custom combinators ------------------------------------------------}

notFollowedBy' :: (Stream s m t, Show a) => ParsecT s u m a -> String -> ParsecT s u m ()
notFollowedBy' p msg = try $ (try p >> unexpected msg) <|> return ()

sepBy1' :: (Stream s m t) => ParsecT s u m Parsec.SourcePos -> ParsecT s u m a -> ParsecT s u m String -> ParsecT s u m (EqnSeq a)
sepBy1' sposP p sep = do
    x <- p
    xs <- many ((,,) <$> sposP <*> sep <*> p)
    return $ eqnSeqFromList x xs


{- Parser ------------------------------------------------------------}
eol :: Parsec [Char] u ()
eol = do
    _ <- try (string "\n\r") <|> try (string "\r\n") <|> string "\n" <|> string "\r" -- <|> (eof >> return "")
        <?> "end of line"
    return ()

wordParser :: String -> Parsec [Char] u String
wordParser expected = many1 (satisfy (not . isSpace)) <?> expected

lineBreak :: Parsec [Char] u ()
lineBreak = (eof <|> eol <|> commentParser) >> manySpacesOrComment

idParser :: Parsec [Char] u String
idParser = idP <?> "Id"
  where
    idP = do
        c <- letter
        cs <- many (char '_' <|> alphaNum)
        lineSpaces
        return (c:cs)

commentParser :: Parsec [Char] u ()
commentParser = p <?> "comment"
  where
    p = do
        _ <- try (string "--")
        _ <- many (noneOf "\r\n")
        eol <|> eof
        return ()

cthyParser :: Parsec [Char] () [ParseDeclTree]
cthyParser = do
    result <- many cthyParsers
    eof
    return result

cthyParsers :: Parsec [Char] () ParseDeclTree
cthyParsers = do
    manySpacesOrComment
    goalParser <|> dataParser <|> axiomParser <|> symParser <|> try funParser

keywordToEolParser :: String -> (String -> a) -> Parsec [Char] () a
keywordToEolParser s f =
    do  keyword s
        result <- trim <$> toEol
        return (f result)

axiomParser :: Parsec [Char] () ParseDeclTree
axiomParser = do
    keyword "axiom"
    name <- idParser
    char ':'
    xs <- trim <$> toEol
    return $ Axiom name xs

dataParser :: Parsec [Char] () ParseDeclTree
dataParser = keywordToEolParser "data" DataDecl

goalParser :: Parsec [Char] () ParseDeclTree
goalParser = keywordToEolParser "goal" Goal

symParser :: Parsec [Char] () ParseDeclTree
symParser = keywordToEolParser "declare_sym" SymDecl

funParser :: Parsec [Char] () ParseDeclTree
funParser = do
    cs <- toEol1 <?> "Function definition"
    return (FunDef cs)

equationProofParser :: Parsec [Char] Env ParseProof
equationProofParser = fmap ParseEquation equationsParser

inductionProofParser :: Parsec [Char] Env ParseProof
inductionProofParser = do
    keyword "on"
    datatype <- wordParser "datatype" 
    lineSpaces
    over <- termParser defaultToFree
    manySpacesOrComment
    cases <- many1 caseParser
    manySpacesOrComment
    return $ ParseInduction datatype over cases

compInductionProofParser :: Parsec [Char] Env ParseProof
compInductionProofParser = do
    keyword "on"
    over <- manyTill (wordParser "variable" <* lineSpaces) (keyword "with")
    fun <- wordParser "function"
    manySpacesOrComment
    cases <- many1 compCaseParser
    manySpacesOrComment
    return $ ParseCompInduction fun over cases

caseProofParser :: Parsec [Char] Env ParseProof
caseProofParser = do
    keyword "on"
    datatype <- many1 (noneOf " \t")
    lineSpaces
    over <- termParser defaultToFree
    manySpacesOrComment
    cases <- many1 caseParser
    manySpacesOrComment
    return $ ParseCases datatype over cases

cheatingProofParser :: Parsec [Char] Env ParseProof
cheatingProofParser = return ParseCheating

extProofParser :: Parsec [Char] Env ParseProof
extProofParser = do
    keyword "with"
    lineSpaces
    with <- termParser defaultToFree
    manySpacesOrComment
    toShow <- toShowParser
    manySpacesOrComment
    proof <- proofParser
    manySpacesOrComment
    return $ ParseExt with toShow proof

type PropParserMode = [String] -> String -> Err RawTerm

propParser :: PropParserMode -> Parsec [Char] Env RawProp
propParser mode = do
    s <- trim <$> toEol1 <?> "expression"
    env <- getState
    let prop = errCtxtStr "Failed to parse expression" $
            iparseProp (mode $ constants env) s
    toParsec show prop

termParser :: PropParserMode -> Parsec [Char] Env RawTerm
termParser mode = flip label "term" $ do
    s <- trim <$> toEol1 <?> "expression"
    env <- getState
    let term = errCtxtStr "Failed to parse expression" $
            iparseTerm (mode $ constants env) s
    toParsec show term

namedPropParser :: PropParserMode -> Parsec [Char] Env String -> Parsec [Char] Env (String, RawProp)
namedPropParser mode p = do
    name <- option "" p
    char ':'
    prop <- propParser mode
    return (name, prop)

lemmaParser :: Parsec [Char] Env ParseLemma
lemmaParser =
    do  keyword "Lemma"
        (name, prop) <- namedPropParser defaultToFree idParser
        manySpacesOrComment
        prf <- proofParser
        manySpacesOrComment
        return $ ParseLemma name prop prf

proofParser :: Parsec [Char] Env ParseProof
proofParser = do
    keyword "Proof"
    p <- choice
        [ keyword "by induction" >> inductionProofParser
        , keyword "by computation induction" >> compInductionProofParser
        , keyword "by extensionality" >> extProofParser
        , keyword "by case analysis" >> caseProofParser
        , keyword "by cheating" >> lineBreak >> cheatingProofParser
        , lineBreak >> equationProofParser
        ]
    keywordQED
    return p

cprfParser ::  Parsec [Char] Env [ParseLemma]
cprfParser =
    do  lemmas <- many1 lemmaParser
        eof
        return lemmas

lineSpaces :: Parsec [Char] u ()
lineSpaces = skipMany (oneOf " \t") <?> "horizontal white space"

keyword :: String -> Parsec [Char] u ()
keyword kw = do
    try (string kw >> notFollowedBy (alphaNum <?> "")) <?> "keyword " ++ show kw
    lineSpaces

keywordCase :: Parsec [Char] u ()
keywordCase = keyword "Case"

keywordQED :: Parsec [Char] u ()
keywordQED = keyword "QED"

toEol :: Parsec [Char] u String
toEol = manyTill anyChar (eof <|> eol <|> commentParser)

toEol1 :: Parsec [Char] u String
toEol1 = do
    notFollowedBy' end "end of line or comment"
    x <- anyChar
    xs <- manyTill anyChar end
    return (x : xs)
  where
    end = eof <|> eol <|> commentParser

byRuleParser :: Parsec [Char] u String
byRuleParser = do
    try (char '(' >>  lineSpaces >> keyword "by")
    cs <- trim <$> manyTill (noneOf "\r\n") (char ')')
    lineSpaces
    return cs

equationsParser :: Parsec [Char] Env (EqnSeqq RawTerm)
equationsParser = do
    eq1 <- equations
    eq2 <- optionMaybe (notFollowedBy keywordQED >> equations)
    return $ EqnSeqq eq1 eq2
  where
    equation = termParser defaultToFree <* manySpacesOrComment
    rule = byRuleParser <* string symPropEq <* lineSpaces
    equations = sepBy1' Parsec.getPosition equation rule

toShowParser :: Parsec [Char] Env RawProp
toShowParser = do
    keyword "To show"
    char ':'
    propParser defaultToFree

caseBodyParser :: Parsec [Char] Env ParseCaseBody
caseBodyParser = do
    toShow <- optionMaybe (toShowParser <* manySpacesOrComment)
    assms <- assmsP
    manySpacesOrComment
    proof <- proofParser
    manySpacesOrComment
    return $ ParseCaseBody toShow assms proof
  where
    assmsP = flip manyTill (lookAhead (string "Proof")) $ do
        assm <- assmP
        manySpacesOrComment
        return assm
    assmP = do
        (name, prop) <- namedPropParser defaultToFree idParser
        return $ Named (if name == "" then "assumption" else name) prop

caseParser :: Parsec [Char] Env ParseCase
caseParser = do
    keywordCase
    lineSpaces
    t <- termParser defaultToFree
    manySpacesOrComment
    ParseCase t <$> caseBodyParser

caseNumParser :: Parsec [Char] u Int
caseNumParser = do
    digits <- many1 digit
    toParsec show (readEither digits)

compCaseParser :: Parsec [Char] Env ParseCompCase
compCaseParser = do
    keywordCase
    lineSpaces
    caseNum <- caseNumParser 
    manySpacesOrComment
    ParseCompCase caseNum <$> caseBodyParser

manySpacesOrComment :: Parsec [Char] u ()
manySpacesOrComment = skipMany $ void space <|> commentParser

instance MonadFail (Either Doc) where
    fail = Left . text

readDataType :: [ParseDeclTree] -> Err [DataType]
readDataType = sequence . mapMaybe parseDataType
  where
    parseDataType (DataDecl s) = Just $ errCtxt (text "Parsing the datatype declaration" <+> quotes (text s)) $ do
        (tycon : dacons) <- traverse parseCons $ splitStringAt "=|" s []
        tyname <- constName $ fst $ stripComb tycon
        dacons' <- traverse (parseDacon tycon) dacons
        return $ DataType tyname dacons'
    parseDataType _ = Nothing

    parseCons :: String -> Err Term
    parseCons = iparseTerm (\x -> Right $ Free (x, 0))

    constName (Const c) = return c
    constName term = errStr $ "Term '" ++ show term ++ "' is not a constant."

    parseDacon tycon term = do
        let (con, args) = stripComb term
        name <- constName con
        args' <- traverse (parseDaconArg tycon) args
        return (name, args')

    parseDaconArg tycon term | term == tycon = return TRec
    parseDaconArg _ (Application _ _) = errStr "Nested constructors (apart from direct recursion) are not allowed."
    parseDaconArg _ (Literal _) = errStr "Literals not allowed in datatype declarations"
    parseDaconArg _ _ = return TNRec

readAxiom :: [String] -> [ParseDeclTree] -> Err [Named Prop]
readAxiom consts = sequence . mapMaybe parseAxiom
  where
    parseAxiom (Axiom n s) = Just $ do
        prop <- iparseProp (defaultToFree consts) s
        return $ Named n $ interpretProp declEnv $ generalizeExceptProp [] prop
    parseAxiom _ = Nothing

readGoal :: [String] -> [ParseDeclTree] -> Err [Prop]
readGoal consts = mapM (fmap $ interpretProp declEnv)  . mapMaybe parseGoal
  where
    parseGoal (Goal s) = Just $ iparseProp (defaultToFree consts) s
    parseGoal _ = Nothing

readSym :: [ParseDeclTree] -> Err [String]
readSym = sequence . mapMaybe parseSym
  where
    parseSym (SymDecl s) = Just $ do
        term <- iparseTerm (Right . Const) s
        case term of
            Const v -> Right v
            _ -> errStr $ "Expression '" ++ s ++ "' is not a symbol"
    parseSym _ = Nothing


readFunc :: [String] -> [ParseDeclTree] -> Err ([Named Prop], [String])
readFunc syms pds = do
    rawDecls <- sequence . mapMaybe parseFunc $ pds
    let syms' = syms ++ map (\(sym, _, _) -> sym) rawDecls
    props0 <- traverse (declToProp syms') rawDecls
    let props = map (fmap $ generalizeExceptProp []) props0
    return (props, syms')
  where

    declToProp :: [String] -> (String, [Exts.Pat SrcSpanInfo], Exts.Exp SrcSpanInfo) -> Err (Named Prop)
    declToProp consts (funSym, pats, rawRhs) = do
        tPat <- traverse translatePat pats
        rhs <- translateExp tv rawRhs
        let prop = interpretProp declEnv $ Prop (listComb (Const funSym) tPat) rhs
        return $ Named ("def " ++ funSym) prop
      where
        pvars = concatMap collectPVars pats
        tv s | s `elem` pvars = return $ Schematic s
             | s `elem` consts = return $ Const s
             | otherwise = errStr $ "Unbound variable '" ++ s ++ "' not allowed on rhs"

    collectPVars :: Exts.Pat l -> [String]
    collectPVars (Exts.PVar _ v) = [translateName v]
    collectPVars (Exts.PInfixApp _ p1 _ p2) = collectPVars p1 ++ collectPVars p2
    collectPVars (Exts.PApp _ _ ps) = concatMap collectPVars ps
    collectPVars (Exts.PList _ ps) = concatMap collectPVars ps
    collectPVars (Exts.PParen _ p) = collectPVars p
    collectPVars _ = []

    parseFunc :: ParseDeclTree -> Maybe (Err (String, [Exts.Pat SrcSpanInfo], Exts.Exp SrcSpanInfo))
    parseFunc (FunDef s) = Just $ errCtxt (text "Parsing function definition" <+> quotes (text s)) $
        case P.parseDecl s of
            P.ParseOk (Exts.FunBind _ [Exts.Match _ name pat (Exts.UnGuardedRhs _ rhs) Nothing])
                -> Right (translateName name, pat, rhs)
            P.ParseOk (Exts.FunBind _ [Exts.InfixMatch _ pat name pats (Exts.UnGuardedRhs _ rhs) Nothing])
                -> Right (translateName name, pat : pats, rhs)
            P.ParseOk (Exts.PatBind _ (Exts.PVar _ name) (Exts.UnGuardedRhs _ rhs) Nothing)
                -> Right (translateName name, [], rhs)
            o@(P.ParseOk _) -> errStr $ unlines [ "Invalid function definition", show o ]
            f@(P.ParseFailed _ _ ) -> err $ renderSrcExtsFail "declaration" f
    parseFunc _ = Nothing

splitStringAt :: Eq a => [a] -> [a] -> [a] -> [[a]]
splitStringAt _ [] h
    | null h = []
    | otherwise = [h]
splitStringAt a (x:xs) h
    | x `elem` a = h : splitStringAt a xs []
    | otherwise = splitStringAt a xs (h++[x])
