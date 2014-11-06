module Test.Info2.Cyp.Parser
    ( ParseLemma (..)
    , ParseCase (..)
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

import Control.Applicative ((<$>))
import Data.Char
import Data.Maybe
import Data.Traversable (traverse)
import Text.Parsec as Parsec
import qualified Language.Haskell.Exts.Parser as P
import qualified Language.Haskell.Exts.Syntax as Exts
import Text.PrettyPrint (quotes, text, (<+>))

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

data ParseLemma = ParseLemma String RawProp ParseProof -- Proposition, Proof

data ParseCase = ParseCase
    { pcCons :: RawTerm
    , pcToShow :: RawProp
    , pcIndHyps :: [Named RawProp]
    , pcProof :: ParseProof
    }

data ParseProof
    = ParseInduction String RawTerm [ParseCase] -- DataTyp, Over, Cases
    | ParseEquation (EqnSeqq RawTerm)


trim :: String -> String
trim = reverse . dropWhile isSpace . reverse . dropWhile isSpace

toParsec :: (a -> String) -> Either a b -> Parsec c u b
toParsec f = either (fail . f) return

eol :: Parsec [Char] u ()
eol = do
    _ <- try (string "\n\r") <|> try (string "\r\n") <|> string "\n" <|> string "\r" -- <|> (eof >> return "")
        <?> "end of line"
    return ()

idParser :: Parsec [Char] u String
idParser = idP <?> "Id"
  where
    idP = do
        c <- lower
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
cthyParser =
    do result <- many cthyParsers
       eof
       return result

cthyParsers :: Parsec [Char] () ParseDeclTree
cthyParsers =
    do manySpacesOrComment
       result <- (goalParser <|> dataParser <|> axiomParser <|> symParser <|> try funParser)
       return result

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
equationProofParser = do
    keyword "Proof"
    eqns <- equationsParser
    manySpacesOrComment
    keywordQED
    return $ ParseEquation eqns

inductionProofParser :: Parsec [Char] Env ParseProof
inductionProofParser =
    do  keyword "Proof by induction on"
        datatype <- many (noneOf " \t")
        lineSpaces
        over <- termParser defaultToFree
        manySpacesOrComment
        cases <- many1 caseParser
        manySpacesOrComment
        keywordQED
        return (ParseInduction datatype over cases)

type PropParserMode = [String] -> String -> Err RawTerm

propParser :: PropParserMode -> Parsec [Char] Env RawProp
propParser mode = do
    s <- trim <$> toEol1
    env <- getState
    let prop = errCtxtStr "Failed to parse expression" $
            iparseProp (mode $ constants env) s
    toParsec show prop

termParser :: PropParserMode -> Parsec [Char] Env RawTerm
termParser mode = do
    s <- trim <$> toEol1
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
proofParser =
  inductionProofParser <|>
  equationProofParser

cprfParser ::  Parsec [Char] Env [ParseLemma]
cprfParser =
    do  lemmas <- many1 lemmaParser
        eof
        return lemmas

lineSpaces :: Parsec [Char] u ()
lineSpaces = skipMany (oneOf " \t") <?> "horizontal white space"

keyword :: String -> Parsec [Char] u ()
keyword kw = try $ do
    _ <- string kw
    notFollowedBy alphaNum
    lineSpaces

keywordCase :: Parsec [Char] u ()
keywordCase = keyword "Case"

keywordQED :: Parsec [Char] u ()
keywordQED = keyword "QED"

toEol :: Parsec [Char] u String
toEol = manyTill anyChar (eof <|> try eol <|> commentParser)

toEol1 :: Parsec [Char] u String
toEol1 = do
    cs <- toEol
    case cs of
        [] -> unexpected "missing text before eol or comment"
        _ -> return cs

byRuleParser :: Parsec [Char] u String
byRuleParser = do
    char '(' >> lineSpaces
    keyword "by"
    cs <- trim <$> manyTill (noneOf "\r\n") (char ')')
    lineSpaces
    return cs

equationsParser :: Parsec [Char] Env (EqnSeqq RawTerm)
equationsParser = do
    eq1 <- equations'
    eq2 <- optionMaybe (try equations')
    return $ EqnSeqq eq1 eq2
  where
    equations' = do
        spaces
        eq <- termParser defaultToFree
        eqs <- many1 (try eqnStep)
        return $ eqnSeqFromList eq eqs
    eqnStep = do
        manySpacesOrComment
        rule <- byRuleParser
        string symPropEq
        lineSpaces
        eq <- termParser defaultToFree
        return (rule, eq)

caseParser :: Parsec [Char] Env ParseCase
caseParser = do
    keywordCase
    lineSpaces
    t <- termParser defaultToFree
    manySpacesOrComment
    toShow <- toShowP
    manySpacesOrComment
    indHyps <- indHypsP
    manySpacesOrComment
    proof <- proofParser
    manySpacesOrComment
    return $ ParseCase
        { pcCons = t
        , pcToShow = toShow
        , pcIndHyps = indHyps
        , pcProof = proof
        }
  where
    toShowP = do
        keyword "To show"
        lineSpaces
        char ':'
        propParser defaultToFree
    indHypsP = many $ do
        hyp <- indHypP
        manySpacesOrComment
        return hyp
    indHypP = do
        string "IH"
        spaces
        (name, prop) <- namedPropParser defaultToFree (many alphaNum)
        return $ Named (if name == "" then "IH" else "IH " ++ name) prop


manySpacesOrComment :: Parsec [Char] u ()
manySpacesOrComment = skipMany $ (space >> return ()) <|> commentParser


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
    parseDaconArg _ (Application _ _) = errStr $ "Nested constructors (apart from direct recursion) are not allowed."
    parseDaconArg _ (Literal _) = errStr $ "Literals not allowed in datatype declarations"
    parseDaconArg _ _ = return TNRec

readAxiom :: [String] -> [ParseDeclTree] -> Err [Named Prop]
readAxiom consts = sequence . mapMaybe parseAxiom
  where
    parseAxiom (Axiom n s) = Just $ do
        prop <- iparseProp (defaultToFree consts) s
        return $ Named n $ interpretProp declEnv $ generalizeExceptProp [] $ prop
    parseAxiom _ = Nothing

readGoal :: [String] -> [ParseDeclTree] -> Err [Prop]
readGoal consts = sequence . map (fmap $ interpretProp declEnv)  . mapMaybe parseGoal
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

    declToProp :: [String] -> (String, [Exts.Pat], Exts.Exp) -> Err (Named Prop)
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

    collectPVars :: Exts.Pat -> [String]
    collectPVars (Exts.PVar v) = [translateName v]
    collectPVars (Exts.PInfixApp p1 _ p2) = collectPVars p1 ++ collectPVars p2
    collectPVars (Exts.PApp _ ps) = concatMap collectPVars ps
    collectPVars (Exts.PList ps) = concatMap collectPVars ps
    collectPVars (Exts.PParen p) = collectPVars p
    collectPVars _ = []

    parseFunc :: ParseDeclTree -> Maybe (Err (String, [Exts.Pat], Exts.Exp))
    parseFunc (FunDef s) = Just $ errCtxt (text "Parsing function definition" <+> quotes (text s)) $
        case P.parseDecl s of
            P.ParseOk (Exts.FunBind [Exts.Match _ name pat _ (Exts.UnGuardedRhs rhs) (Exts.BDecls [])])
                -> Right (translateName name, pat, rhs)
            P.ParseOk _ -> errStr "Invalid function definition."
            f@(P.ParseFailed _ _ ) -> errStr $ show f
    parseFunc _ = Nothing

splitStringAt :: Eq a => [a] -> [a] -> [a] -> [[a]]
splitStringAt _ [] h
    | h == [] = []
    | otherwise = h : []
splitStringAt a (x:xs) h
    | x `elem` a = h : splitStringAt a xs []
    | otherwise = splitStringAt a xs (h++[x])
