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
import Data.Bifunctor.Biff (Biff (..))
import Data.Char (isAlpha, isAlphaNum, isSymbol)
import qualified Data.Dependent.Map as DMap
import Data.Functor (void, (<&>))
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.HashSet (HashSet)
import qualified Data.HashSet as HS
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty.Utils as NE
import qualified Data.Map as Map
import Data.Semigroup
import qualified Data.Set as Set
import Data.Some (Some (..))
import Data.Text (Text)
import qualified Data.Text as T
import Data.Void (Void)
import Language.Lambda.Syntax.LambdaPi
import Text.Megaparsec (Parsec, between, eof, errorBundlePretty, label, notFollowedBy, runParser, satisfy, takeWhileP, try, (<?>))
import Text.Megaparsec.Char (space1, string)
import Text.Megaparsec.Char.Lexer (decimal, skipBlockCommentNested, skipLineComment)
import qualified Text.Megaparsec.Char.Lexer as L

type VarMap = HashMap Text Int

type Parser = ReaderT VarMap (Parsec Void Text)

operators :: [[HOperator SMode Parser Term]]
operators =
  [
    [ infixR theMode theMode theMode $
        (:::) <$ reservedOp ":"
    ]
  ,
    [ InfixR theMode theMode theMode $
        (~>) <$ (reservedOp "->" <|> reservedOp "→")
    ]
  ,
    [ infixL theMode theMode theMode $
        (:@:) <$ try appSpaceP
    ]
  ]

(~>) ::
  Term 'Checkable ->
  Parser (Term 'Checkable) ->
  Parser (Term 'Inferable)
(~>) l p = Pi l <$> anonymousBind p

{-
>>> parseOnly inferableExprP "Nat -> Nat"
Right (Pi (Inf Nat) (Inf Nat))

>>> parseOnly checkableExprP "Nat -> Nat"
Right (Inf (Pi (Inf Nat) (Inf Nat)))

>>> parseOnly checkableExprP "(Nat -> Nat)"
Right (Inf (Pi (Inf Nat) (Inf Nat)))

>>> parseOnly inferableExprP "(λ x. x) -> Nat"
Right (Pi (Lam (Inf (Bound 0))) (Inf Nat))

>>> parseOnly checkableExprP "Nat"
Right (Inf Nat)

>>> parseOnly inferableExprP "Nat : Type"
Right (Inf Nat ::: Inf Star)

>>> parseOnly checkableExprP "Nat : Type"
Right (Inf (Inf Nat ::: Inf Star))

>>> parseOnly checkableExprP "(Nat : Type)"
Right (Inf (Inf Nat ::: Inf Star))
-}
appSpaceP :: Parser ()
appSpaceP =
  space <* notFollowedBy (satisfy isOperatorSymbol)

reservedOpNames :: HashSet Text
reservedOpNames = HS.fromList ["->", "→", ":", "#"]

exprCasters :: CastFunctions SMode Term
exprCasters = DMap.singleton SInferable (Compose (DMap.singleton SCheckable $ Biff Inf))

exprParsers :: ParserDict SMode Parser Term
exprParsers =
  makeHExprParser
    (Set.fromList [Some SInferable, Some SCheckable])
    exprCasters
    basicTermParsers
    operators

inferableExprP :: Parser (Term 'Inferable)
inferableExprP = parserOf exprCasters SInferable exprParsers

checkableExprP :: Parser (Term 'Checkable)
checkableExprP = parserOf exprCasters SCheckable exprParsers

basicTermParsers :: ParserDict SMode Parser Term
basicTermParsers =
  DMap.fromList
    [ SInferable
        ~=> ( atomicInfTerms <|> parens inferableExprP
            )
    , SCheckable
        ~=> ( try unAnnLamP
                <|> recordChkP
                <|> parens checkableExprP
            )
    ]
  where
    atomicInfTerms =
      piP
        <|> try lamAnnP
        <|> primTypeP
        <|> compoundTyConP
        <|> datConP
        <|> eliminatorsP
        <|> varP

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
    T.pack <$> some (satisfy isOperatorSymbol)

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

primTypeP :: Parser (Term 'Inferable)
primTypeP =
  label "Primitive type" $
    Star <$ (reserved "Type" <|> reserved "★")
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
lamAnnP = label "Typed lambda abstraction" $ do
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
      ( Variant <$> fieldSeqP "tag" (try (symbol "|" <* notFollowedBy (symbol ")"))) (symbol ":")
      )
    <|> between (symbol "{") (symbol "}") (Record <$> fieldSeqP "field" (symbol ",") (symbol ":"))

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

variantBracketed :: Parser a -> Parser a
variantBracketed p =
  try (symbol "(" *> symbol "|" *> p <* (symbol "|" *> symbol ")"))
    <|> symbol "⦇" *> p <* symbol "⦈"

datConP :: Parser (Term 'Inferable)
datConP =
  naturalP
    <|> LamAnn Star' (Nil (Bound' 0)) <$ reserved "nil"
    <|> LamAnn Nat' (Succ (Bound' 0)) <$ reserved "succ"
    <|> cons' <$ reserved "cons"

naturalP :: Parser (Term 'Inferable)
naturalP =
  lexeme decimal <&> \n ->
    foldr ($) Zero (replicate n (Succ . Inf))

recordChkP :: Parser (Term 'Checkable)
recordChkP =
  reserved "record"
    *> between
      (symbol "{")
      (symbol "}")
      (MkRecord <$> fieldSeqP "field" (symbol ",") (symbol "="))

unAnnLamP :: Parser (Term 'Checkable)
unAnnLamP = label "Unannotated lambda" $ lexeme $ do
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
parseOnly = parseNamed "<input>" . (<* eof) . (space *>)

parseNamed ::
  String ->
  Parser a ->
  Text ->
  Either String a
parseNamed name p = (errorBundlePretty +++ id) . runParser (runReaderT p mempty) name
