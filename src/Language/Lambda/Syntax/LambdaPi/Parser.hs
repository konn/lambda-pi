{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}

module Language.Lambda.Syntax.LambdaPi.Parser where

import Control.Applicative (Alternative (..))
import Control.Applicative.Combinators (sepBy)
import qualified Control.Applicative.Combinators.NonEmpty as NE
import Control.Arrow ((+++))
import Control.Monad (unless, when)
import Control.Monad.Combinators.Expr.HigherKinded
import Control.Monad.Trans.Reader (ReaderT (runReaderT), asks, local)
import qualified Data.Bifunctor as Bi
import Data.Char (isAlphaNum, isLetter)
import qualified Data.Dependent.Map as DMap
import Data.Functor (void, (<&>))
import Data.Functor.Apply
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty.Utils as NE
import qualified Data.Map as Map
import Data.Semigroup
import Data.Semigroup.Foldable (asum1)
import qualified Data.Set as Set
import Data.Some (Some (..))
import Data.Text (Text)
import qualified Data.Text as T
import Data.Void (Void)
import Language.Lambda.Syntax.LambdaPi
import Text.Megaparsec (Parsec, between, errorBundlePretty, label, notFollowedBy, runParser, satisfy, takeWhileP, try, (<?>))
import Text.Megaparsec.Char (space1, string)
import Text.Megaparsec.Char.Lexer (decimal, skipBlockCommentNested, skipLineComment)
import qualified Text.Megaparsec.Char.Lexer as L

type VarMap = HashMap Text Int

type Parser = ReaderT VarMap (Parsec Void Text)

operators :: [[HOperator SMode Parser Term]]
operators =
  [
    [ infixR theMode theMode theMode $
        (:::) <$ reserved ":"
    ]
  ,
    [ InfixR theMode theMode theMode $
        ( \l p ->
            Pi l <$> anonymousBind p
        )
          <$ (reserved "->" <|> reserved "→")
    ]
    {- ,
      [ infixL theMode theMode theMode $
          (:@:) <$ appSpaceP
      ] -}
  ]

appSpaceP :: Parser ()
appSpaceP =
  notFollowedBy (unwrapApplicative $ asum1 $ NE.map (WrapApplicative . symbol) opNames)

opNames :: NonEmpty Text
opNames = NE.fromList ["->", "→", ":", "#"]

exprParsers :: ParserDict SMode Parser Term
exprParsers =
  makeHExprParser (Set.fromList [Some SInferable, Some SCheckable]) basicTermParsers operators

basicTermParsers :: ParserDict SMode Parser Term
basicTermParsers =
  DMap.fromList
    [ SInferable
        ~=> piP
        <|> try lamAnnP
        <|> primTypeP
        <|> compoundTyConP
        <|> datConP
        <|> eliminatorsP
        <|> varP
        <|> parens (parserOf SInferable exprParsers)
    , SCheckable
        ~=> try unAnnLamP
        <|> try recordChkP
        <|> try (Inf <$> parserOf theMode basicTermParsers)
        <|> parens (parserOf SCheckable exprParsers)
    ]

binding :: Text -> Parser a -> Parser a
binding v = local (HM.insert v 0 . HM.map succ)

anonymousBind :: Parser a -> Parser a
anonymousBind = local $ HM.map succ

space :: Parser ()
space =
  L.space
    space1
    (skipLineComment "--")
    (skipBlockCommentNested "{-" "-}")

keywords :: HS.HashSet Text
keywords = HS.fromList ["λ", "Π", "natElim", "0", "succ", "zero", "vecElim", "nil", "cons", "ℕ", "Nat", "Vec", "Type", "record", "->", "→", ":"]

isIdentHeadChar :: Char -> Bool
isIdentHeadChar ch = isLetter ch || ch == '_'

isIdentBodyChar :: Char -> Bool
{-# INLINE isIdentBodyChar #-}
isIdentBodyChar ch = ch == '_' || ch == '-' || isAlphaNum ch

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
  lexeme $
    try $ do
      ident <- identifierLike
      when (ident `HS.member` keywords) $ do
        fail $ "Identifier expected, but got keyword: " <> T.unpack ident
      pure ident

lexeme :: Parser a -> Parser a
lexeme = L.lexeme space

parens :: Parser a -> Parser a
parens = between (symbol "(" <* notFollowedBy (symbol "|")) (symbol ")")

symbol :: Text -> Parser Text
symbol = L.symbol space

primTypeP :: Parser (Term 'Inferable)
primTypeP =
  label "Primitive type" $
    Star <$ (reserved "*" <|> reserved "Type" <|> reserved "★")
      <|> Nat <$ (reserved "ℕ" <|> reserved "Nat")

varP :: Parser (Term 'Inferable)
varP = do
  ident <- identifier <?> "variable"
  mb <- asks (HM.lookup ident)
  pure $ case mb of
    Just i -> Bound i
    Nothing -> Free $ Global ident

binder :: Parser (NonEmpty (Text, Term 'Checkable))
binder =
  parens
    ( flip (fmap . flip (,))
        <$> NE.some identifier
        <* symbol ":"
        <*> (checkableExprP <?> "variable type")
    )

binders :: Parser (NonEmpty (Text, Term 'Checkable))
binders = sconcat <$> NE.some binder

lamAnnP :: Parser (Term 'Inferable)
lamAnnP = label "Typed lambda abstraction" $
  lexeme $
    try $ do
      reserved "λ"
      bindees <- binders <* symbol "."
      foldr (\(var, ty) p -> binding var $ LamAnn ty <$> p) inferableExprP bindees

piP :: Parser (Term 'Inferable)
piP = label "Pi-binding" $ do
  reserved "Π"
  bindees <- binders <* symbol "."
  let (half, (var0, ty0)) = NE.unsnoc bindees
  foldr
    (\(var, ty) p -> binding var $ Pi ty . Inf <$> p)
    (binding var0 $ Pi ty0 <$> checkableExprP)
    half

eliminatorsP :: Parser (Term 'Inferable)
eliminatorsP =
  natElim' <$ reserved "natElim"
    <|> vecElim' <$ reserved "vecElim"

compoundTyConP :: Parser (Term 'Inferable)
compoundTyConP =
  vecCon' <$ reserved "Vec"
    <|> variantBracketed
      ( Variant <$> fieldSeqP "tag" (symbol "|" <* notFollowedBy (symbol ")")) (symbol ":")
      )
    <|> try (between (symbol "{") (symbol "}") (Record <$> fieldSeqP "field" (symbol ",") (symbol ":")))

fieldSeqP ::
  String ->
  Parser fieldSeparator ->
  Parser fieldAndTypeSep ->
  Parser [(Text, Term 'Checkable)]
fieldSeqP tokenName sep fldSep = do
  flds <-
    ( (,)
        <$> (identifier <?> tokenName)
        <* fldSep
        <*> checkableExprP
      )
      `sepBy` try sep
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

variantBracketed :: Parser a -> Parser a
variantBracketed p =
  try (symbol "(" *> symbol "|" *> p <* try (symbol "|" *> symbol ")"))
    <|> symbol "⦇" *> p <* symbol "⦈"

datConP :: Parser (Term 'Inferable)
datConP =
  naturalP
    <|> LamAnn Star' (Nil (Bound' 0)) <$ reserved "nil"
    <|> LamAnn Nat' (Succ (Bound' 0)) <$ reserved "succ"
    <|> cons' <$ reserved "cons"

inferableExprP :: Parser (Term 'Inferable)
inferableExprP = parserOf theMode exprParsers

naturalP :: Parser (Term 'Inferable)
naturalP =
  lexeme decimal <&> \n ->
    foldr ($) Zero (replicate n (Succ . Inf))

checkableExprP :: Parser (Term 'Checkable)
checkableExprP = parserOf theMode exprParsers

recordChkP :: Parser (Term 'Checkable)
recordChkP =
  reserved "record"
    *> between
      (symbol "{")
      (symbol "}")
      (MkRecord <$> fieldSeqP "field" (symbol ",") (symbol "="))

unAnnLamP :: Parser (Term 'Checkable)
unAnnLamP = label "Unannotated lambda" $
  lexeme $
    try $ do
      reserved "λ"
      bindee <- some (identifier <?> "variable name")
      void $ symbol "."
      foldr
        (\var p -> binding var $ Lam <$> p)
        (checkableExprP <?> "lambda body")
        bindee

parseOnly ::
  Parser a ->
  Text ->
  Either String a
parseOnly = parseNamed "<input>"

parseNamed ::
  String ->
  Parser a ->
  Text ->
  Either String a
parseNamed name p = (errorBundlePretty +++ id) . runParser (runReaderT p mempty) name
