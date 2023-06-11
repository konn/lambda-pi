{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TupleSections #-}

module Language.Lambda.Syntax.LambdaPi.TreesThatGrow.Parser (
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
import qualified Control.Applicative.Combinators.NonEmpty as NE
import Control.Arrow ((+++))
import Control.Monad
import Control.Monad.Combinators.Expr
import qualified Data.Bifunctor as Bi
import Data.Char
import Data.Functor
import Data.HashSet (HashSet)
import qualified Data.HashSet as HS
import Data.List (foldl1')
import Data.List.NonEmpty (NonEmpty)
import qualified Data.Map.Strict as Map
import Data.Semigroup
import Data.Semigroup.Foldable (fold1)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Void (Void)
import Language.Lambda.Syntax.LambdaPi.TreesThatGrow
import Text.Megaparsec (Parsec, between, eof, errorBundlePretty, label, notFollowedBy, runParser, satisfy, takeWhile1P, takeWhileP, try, (<?>))
import Text.Megaparsec.Char (space1, string)
import Text.Megaparsec.Char.Lexer (decimal, skipBlockCommentNested, skipLineComment)
import qualified Text.Megaparsec.Char.Lexer as L

type Parser = Parsec Void Text

type ParsedExpr = Expr Parse

exprP :: Parser ParsedExpr
exprP =
  makeExprParser
    termP
    [
      [ InfixR $
          Pi NoExtField Indep
            <$ (reservedOp "->" <|> reservedOp "→")
      ]
    , [InfixR $ Ann NoExtField <$ reservedOp ":"]
    , [InfixL $ App NoExtField <$ appSpaceP]
    , [Postfix fieldProjsP]
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
termP = piP <|> primTypeP <|> compoundTyConP <|> dataConP <|> eliminatorsP <|> lamP <|> varP <|> parens exprP

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
  natElim' <$ reserved "natElim"
    <|> vecElim' <$ reserved "vecElim"

natElim' :: ParsedExpr
natElim' =
  Lam NoExtField "t" (Just (Pi NoExtField Indep nat star))
    $ Lam NoExtField "base" (Just (App NoExtField (var "t") zero))
    $ Lam
      NoExtField
      "ind"
      ( Just
          ( Pi
              NoExtField
              (DepNamed "k")
              nat
              ( Pi
                  NoExtField
                  Indep
                  (App NoExtField (var "t") (var "k"))
                  $ App NoExtField (var "t")
                  $ succ' (var "k")
              )
          )
      )
    $ Lam NoExtField "n" (Just nat)
    $ NatElim NoExtField (var "t") (var "base") (var "ind") (var "n")

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
                  apps [var "t", Succ NoExtField (var "n"), Cons NoExtField (var "a") (var "n") (var "x") (var "xs")]
      )
    $ Lam NoExtField "n" (Just nat)
    $ Lam NoExtField "xs" (Just $ Vec NoExtField (var "a") (var "n"))
    $ apps [var "t", var "n", var "xs"]

apps :: [ParsedExpr] -> Expr Parse
apps = foldl1' (App NoExtField)

dataConP :: Parser ParsedExpr
dataConP =
  naturalP
    <|> Lam NoExtField "t" (Just star) (Nil NoExtField (var "t")) <$ reserved "nil"
    <|> Zero NoExtField <$ reserved "zero"
    <|> Lam NoExtField "n" (Just nat) (succ' $ var "n") <$ reserved "succ"
    <|> cons' <$ reserved "cons"
    <|> recordP

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
var = Var NoExtField

naturalP :: Parser ParsedExpr
naturalP =
  lexeme decimal <&> \n ->
    foldr ($) zero (replicate n succ')

succ' :: ParsedExpr -> ParsedExpr
succ' = Succ NoExtField

zero :: ParsedExpr
zero = Zero NoExtField

nat :: Expr Parse
nat = Nat NoExtField

star :: Expr Parse
star = Star NoExtField

compoundTyConP :: Parser ParsedExpr
compoundTyConP =
  vecCon' <$ reserved "Vec"
    <|> between (symbol "{") (symbol "}") (Record NoExtField . RecordFieldTypes <$> fieldSeqP "field" (symbol ",") (symbol ":"))

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
vecCon' = Lam NoExtField "t" (Just (Star NoExtField)) $ Lam NoExtField "n" (Just (Nat NoExtField)) $ Vec NoExtField (Var NoExtField "t") (Var NoExtField "n")

varP :: Parser ParsedExpr
varP = Var NoExtField <$> identifier

primTypeP :: Parser ParsedExpr
primTypeP =
  label "Primitive type" $
    Star NoExtField <$ (reserved "Type" <|> reserved "★")
      <|> Nat NoExtField <$ (reserved "ℕ" <|> reserved "Nat")

space :: Parser ()
space =
  L.space
    space1
    (skipLineComment "--")
    (skipBlockCommentNested "{-" "-}")

keywords :: HS.HashSet Text
keywords = HS.fromList ["λ", "Π", "natElim", "0", "succ", "zero", "vecElim", "nil", "cons", "ℕ", "Nat", "Vec", "Type", "record"]

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
parens = between (symbol "(" <* notFollowedBy (symbol "|")) (symbol ")")

symbol :: Text -> Parser Text
symbol = L.symbol space

reservedOpNames :: HashSet Text
reservedOpNames = HS.fromList ["->", "→", ":", "#"]

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
