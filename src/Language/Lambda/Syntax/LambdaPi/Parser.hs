{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}

-- FIXME: let-and-app test case suffers
module Language.Lambda.Syntax.LambdaPi.Parser (
  -- * ASTs,
  Parse,
  ParsedExpr,
  ParsedName (..),

  -- * Parsers
  exprP,
  Parser,
  parseOnly,
  parseNamed,

  -- * Misc
  space,
  symbol,
  operator,
  identifier,
  binders,
  reservedOp,
  reserved,
  keywords,
  reservedOpNames,
) where

import Control.Applicative (Alternative (..))
import Control.Applicative.Combinators (sepBy)
import Control.Applicative.Combinators.NonEmpty qualified as NE
import Control.Arrow ((+++))
import Control.Monad
import Control.Monad.Combinators.Expr
import Data.Bifunctor qualified as Bi
import Data.Char
import Data.Data (Data)
import Data.Functor
import Data.HashSet (HashSet)
import Data.HashSet qualified as HS
import Data.List (foldl1')
import Data.List.NonEmpty (NonEmpty)
import Data.Map.Strict qualified as Map
import Data.Semigroup
import Data.Semigroup.Foldable (fold1)
import Data.String
import Data.Text (Text)
import Data.Text qualified as T
import Data.Void (Void)
import GHC.Generics (Generic)
import Language.Lambda.Syntax.LambdaPi
import RIO (tshow)
import Text.Megaparsec (Parsec, between, eof, errorBundlePretty, label, notFollowedBy, runParser, satisfy, takeWhile1P, takeWhileP, try, (<?>))
import Text.Megaparsec.Char (space1, string)
import Text.Megaparsec.Char.Lexer (decimal, skipBlockCommentNested, skipLineComment)
import Text.Megaparsec.Char.Lexer qualified as L
import Text.PrettyPrint.Monadic (Pretty (..))

type Parser = Parsec Void Text

type ParsedExpr = Expr Parse

exprP :: Parser ParsedExpr
exprP =
  makeExprParser
    termP
    [ [Postfix fieldProjsP]
    , [InfixL $ App NoExtField <$ appSpaceP]
    , [InfixR $ Ann NoExtField <$ reservedOp ":"]
    ,
      [ InfixR $
          Pi NoExtField Indep
            <$ (reservedOp "->" <|> reservedOp "→")
      ]
    ]

fieldProjsP :: Parser (ParsedExpr -> ParsedExpr)
fieldProjsP =
  appEndo . getDual . fold1
    <$> NE.some (string "." *> identifier <&> \fld -> Dual $ Endo $ flip (ProjField NoExtField) fld)

appSpaceP :: Parser ()
appSpaceP =
  space
    <* notFollowedBy
      ( satisfy $
          \ch ->
            isOperatorSymbol ch
              || generalCategory ch == ClosePunctuation
      )

termP :: Parser ParsedExpr
termP = piP <|> primTypeP <|> compoundTyConP <|> dataConP <|> eliminatorsP <|> letP <|> caseP <|> lamP <|> varP <|> parens exprP

openP :: Parser ParsedExpr
openP =
  label "open expression" $
    Open NoExtField
      <$ reserved "open"
      <*> exprP
      <* between (symbol "{") (symbol "}") (reserved "..")
      <* reserved "in"
      <*> exprP

letP :: Parser ParsedExpr
letP =
  label "let-expression" $
    Let NoExtField
      <$ reserved "let"
      <*> identifier
      <* reservedOp "="
      <*> exprP
      <* reserved "in"
      <*> exprP

caseP :: Parser ParsedExpr
caseP =
  label "case-expression" $
    Case NoExtField
      <$ reserved "case"
      <*> exprP
      <* reserved "of"
      <*> between
        (symbol "{")
        (symbol "}")
        (CaseAlts <$> (caseAltP `sepBy` symbol ";"))

caseAltP :: Parser (Text, CaseAlt Parse)
caseAltP =
  (,)
    <$> identifier
    <*> ( CaseAlt NoExtField
            <$> identifier
            <* (reservedOp "→" <|> reservedOp "->")
            <*> exprP
        )

piP :: Parser ParsedExpr
piP = label "Pi-binding" $ do
  reserved "Π"
  bindees <- sconcat <$> NE.some annBinder <* symbol "."
  foldr
    (\(v, ty) p -> Pi NoExtField (DepNamed v) ty <$> p)
    exprP
    bindees

lamP :: Parser ParsedExpr
lamP = do
  reserved "λ"
  bndrs <- binders <* symbol "."
  foldr
    (\(v, mty) p -> Lam NoExtField v mty <$> p)
    exprP
    bndrs

binders :: Parser (NonEmpty (Text, Maybe ParsedExpr))
binders = sconcat <$> NE.some binder

binder :: Parser (NonEmpty (Text, Maybe ParsedExpr))
binder =
  parens
    ( flip (fmap . flip (,))
        <$> NE.some identifier
        <* symbol ":"
        <*> (Just <$> exprP <?> "variable type")
    )
    <|> fmap (,Nothing) <$> NE.some identifier

annBinder :: Parser (NonEmpty (Text, ParsedExpr))
annBinder =
  parens
    ( flip (fmap . flip (,))
        <$> NE.some identifier
        <* symbol ":"
        <*> exprP
        <?> "variable type"
    )

eliminatorsP :: Parser ParsedExpr
eliminatorsP =
  Prim NatElim <$ reserved "natElim"
    <|> vecElim' <$ reserved "vecElim"
    <|> try openP

vecElim' :: ParsedExpr
vecElim' =
  Lam NoExtField "a" (Just star)
    $ Lam
      NoExtField
      "t"
      ( Just $
          Pi NoExtField (DepNamed "n") nat $
            Pi
              NoExtField
              Indep
              (Vec NoExtField (var "a") (var "n"))
              star
      )
    $ Lam
      NoExtField
      "base"
      ( Just $ apps [var "t", zero, Nil NoExtField (var "a")]
      )
    $ Lam
      NoExtField
      "ind"
      ( Just $
          Pi NoExtField (DepNamed "n") nat $
            Pi NoExtField (DepNamed "x") (var "a") $
              Pi NoExtField (DepNamed "xs") (Vec NoExtField (var "a") (var "n")) $
                Pi NoExtField Indep (apps [var "t", var "n", var "xs"]) $
                  apps [var "t", Succ' (var "n"), Cons NoExtField (var "a") (var "n") (var "x") (var "xs")]
      )
    $ Lam NoExtField "n" (Just nat)
    $ Lam NoExtField "xs" (Just $ Vec NoExtField (var "a") (var "n"))
    $ apps [var "t", var "n", var "xs"]

pattern Succ' :: Expr Parse -> Expr Parse
pattern Succ' e = App NoExtField (Prim Succ) e

pattern Prim :: Prim -> Expr Parse
pattern Prim p = Var NoExtField (Primitive p)

apps :: [ParsedExpr] -> Expr Parse
apps = foldl1' (App NoExtField)

dataConP :: Parser ParsedExpr
dataConP =
  naturalP
    <|> Lam NoExtField "t" (Just star) (Nil NoExtField (var "t")) <$ reserved "nil"
    <|> Prim Zero <$ reserved "zero"
    <|> Prim Succ <$ reserved "succ"
    <|> cons' <$ reserved "cons"
    <|> recordP
    <|> varInjP

recordP :: Parser ParsedExpr
recordP =
  MkRecord NoExtField
    <$ reserved "record"
    <*> between
      (symbol "{")
      (symbol "}")
      (MkRecordFields <$> fieldSeqP "field" (symbol ",") (symbol "="))

cons' :: ParsedExpr
cons' =
  Lam
    NoExtField
    "t"
    (Just star)
    $ Lam NoExtField "n" (Just nat)
    $ Lam NoExtField "x" (Just (var "t"))
    $ Lam NoExtField "xs" (Just (Vec NoExtField (var "t") (var "n")))
    $ Cons NoExtField (var "t") (var "n") (var "x") (var "xs")

var :: Text -> ParsedExpr
var = Var NoExtField . Ident

naturalP :: Parser ParsedExpr
naturalP =
  lexeme decimal <&> \n ->
    foldr ($) zero (replicate n succ')

succ' :: ParsedExpr -> ParsedExpr
succ' = Succ'

zero :: ParsedExpr
zero = Prim Zero

nat :: Expr Parse
nat = Prim Nat

star :: Expr Parse
star = Star NoExtField

compoundTyConP :: Parser ParsedExpr
compoundTyConP = vecCon' <$ reserved "Vec" <|> recordTyP <|> variantTyP

recordTyP :: Parser ParsedExpr
recordTyP = try (between (symbol "{") (symbol "}") (Record NoExtField . RecordFieldTypes <$> fieldSeqP "field" (symbol ",") (symbol ":")))

variantTyP :: Parser ParsedExpr
variantTyP = try (between (symbol "(|") (symbol "|)") (Variant NoExtField . VariantTags <$> fieldSeqP "tag" (try $ symbol "|" <* notFollowedBy (symbol ")")) (symbol ":")))

varInjP :: Parser ParsedExpr
varInjP =
  try $
    between (symbol "(|") (symbol "|)") $
      Inj NoExtField <$> identifier <* reservedOp "=" <*> exprP

fieldSeqP ::
  String ->
  Parser fieldSeparator ->
  Parser fieldAndTypeSep ->
  Parser [(Text, ParsedExpr)]
fieldSeqP tokenName sep fldSep = do
  flds <-
    ( (,)
        <$> (identifier <?> tokenName)
        <* fldSep
        <*> exprP
      )
      `sepBy` sep
  let dups =
        map fst $
          filter ((> 1) . snd) $
            Map.toList $
              Map.fromListWith (+) $
                map (Bi.second $ const (1 :: Int)) flds
  unless (null dups) $
    fail $
      "Following field(s) occurred more than once: "
        <> show dups
  pure flds

vecCon' :: ParsedExpr
vecCon' = Lam NoExtField "t" (Just (Star NoExtField)) $ Lam NoExtField "n" (Just nat) $ Vec NoExtField (Var NoExtField "t") (Var NoExtField "n")

varP :: Parser ParsedExpr
varP = Var NoExtField . Ident <$> identifier

primTypeP :: Parser ParsedExpr
primTypeP =
  label "Primitive type" $
    Star NoExtField <$ (reserved "Type" <|> reserved "★")
      <|> nat <$ (reserved "ℕ" <|> reserved "Nat")

space :: Parser ()
space =
  L.space
    space1
    (skipLineComment "--")
    (skipBlockCommentNested "{-" "-}")

keywords :: HS.HashSet Text
keywords = HS.fromList ["λ", "Π", "natElim", "0", "succ", "zero", "vecElim", "nil", "cons", "ℕ", "Nat", "Vec", "Type", "record", "open", "in", "let", "case", "of"]

isIdentHeadChar :: Char -> Bool
isIdentHeadChar ch = isAlpha ch || ch == '_' || ch == '★'

isIdentBodyChar :: Char -> Bool
{-# INLINE isIdentBodyChar #-}
isIdentBodyChar ch = ch == '_' || isAlphaNum ch

identifierLike :: Parser Text
identifierLike =
  lexeme $
    T.cons <$> satisfy isIdentHeadChar <*> takeWhileP (Just "token String") isIdentBodyChar

reserved :: Text -> Parser ()
reserved name =
  lexeme $
    try $
      void $
        string name <* notFollowedBy (satisfy isIdentBodyChar)

identifier :: Parser Text
identifier = label "identifier" $
  try $ do
    ident <- identifierLike
    when (ident `HS.member` keywords) $ do
      fail $ "Identifier expected, but got keyword: " <> T.unpack ident
    pure ident

operatorLike :: Parser Text
operatorLike =
  lexeme $
    takeWhile1P (Just "operator symbol") isOperatorSymbol

isOperatorSymbol :: Char -> Bool
isOperatorSymbol c =
  isSymbol c && not (c `HS.member` HS.fromList "★")
    || c `HS.member` HS.fromList "*/-_><+#:?!."

reservedOp :: Text -> Parser ()
reservedOp name =
  void $ lexeme $ string name <* notFollowedBy (satisfy isOperatorSymbol)

operator :: Parser Text
operator = label "operator" $ try $ do
  name <- operatorLike
  when (name `HS.member` reservedOpNames) $
    fail $
      "Reserved operator name found: " <> T.unpack name
  pure name

lexeme :: Parser a -> Parser a
lexeme = L.lexeme space

parens :: Parser a -> Parser a
parens = try . between (symbol "(" <* notFollowedBy (symbol "|")) (symbol ")")

symbol :: Text -> Parser Text
symbol = L.symbol space

reservedOpNames :: HashSet Text
reservedOpNames = HS.fromList ["->", "→", ":", "#", "|", "="]

parseOnly ::
  Parser a ->
  Text ->
  Either String a
parseOnly = parseNamed "<input>" . (<* eof) . (space *>)

parseNamed ::
  String ->
  Parser a ->
  Text ->
  Either String a
parseNamed name p = (errorBundlePretty +++ id) . runParser p name

data Parse deriving (Show, Eq, Ord, Generic, Data)

type instance XAnn Parse = NoExtField

type instance AnnLHS Parse = Expr Parse

type instance AnnRHS Parse = Expr Parse

type instance XStar Parse = NoExtField

type instance XVar Parse = NoExtField

type instance Id Parse = ParsedName

data ParsedName
  = Ident !Text
  | Primitive Prim
  deriving (Show, Eq, Ord, Generic, Data)

instance Pretty e ParsedName where
  pretty (Ident t) = pretty t
  pretty (Primitive p) = pretty p

instance VarLike ParsedName where
  varName (Ident t) = pure $ Just t
  varName (Primitive p) = pure $ Just $ tshow $ pprint p

instance IsString ParsedName where
  fromString "succ" = Primitive Succ
  fromString "zero" = Primitive Zero
  fromString "Unit" = Primitive Unit
  fromString "tt" = Primitive Tt
  fromString ident = Ident $ T.pack ident

type instance XApp Parse = NoExtField

type instance AppLHS Parse = Expr Parse

type instance AppRHS Parse = Expr Parse

type instance XLam Parse = NoExtField

type instance LamBindName Parse = Text

type instance LamBindType Parse = Maybe (Expr Parse)

type instance LamBody Parse = Expr Parse

type instance XPi Parse = NoExtField

type instance PiVarName Parse = DepName

type instance PiVarType Parse = Expr Parse

type instance PiRHS Parse = Expr Parse

type instance XLet Parse = NoExtField

type instance LetName Parse = Text

type instance LetRHS Parse = Expr Parse

type instance LetBody Parse = Expr Parse

type instance XVec Parse = NoExtField

type instance VecType Parse = Expr Parse

type instance VecLength Parse = Expr Parse

type instance XNil Parse = NoExtField

type instance NilType Parse = Expr Parse

type instance XCons Parse = NoExtField

type instance ConsType Parse = Expr Parse

type instance ConsLength Parse = Expr Parse

type instance ConsHead Parse = Expr Parse

type instance ConsTail Parse = Expr Parse

type instance XVecElim Parse = NoExtField

type instance VecElimEltType Parse = Expr Parse

type instance VecElimRetFamily Parse = Expr Parse

type instance VecElimBaseCase Parse = Expr Parse

type instance VecElimInductiveStep Parse = Expr Parse

type instance VecElimLength Parse = Expr Parse

type instance VecElimInput Parse = Expr Parse

type instance XRecord Parse = NoExtField

type instance RecordFieldType Parse = Expr Parse

type instance XProjField Parse = NoExtField

type instance ProjFieldRecord Parse = Expr Parse

type instance XMkRecord Parse = NoExtField

type instance RecordField Parse = Expr Parse

type instance XOpen Parse = NoExtField

type instance OpenRecord Parse = Expr Parse

type instance OpenBody Parse = Expr Parse

type instance XVariant Parse = NoExtField

type instance VariantArgType Parse = Expr Parse

type instance XInj Parse = NoExtField

type instance InjArg Parse = Expr Parse

type instance XCase Parse = NoExtField

type instance CaseArg Parse = Expr Parse

type instance XCaseAlt Parse = NoExtField

type instance CaseAltVarName Parse = Text

type instance CaseAltBody Parse = Expr Parse

type instance XExpr Parse = NoExtCon
