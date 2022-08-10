{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Language.Lambda.Syntax.LambdaPi.Parser where

import Control.Applicative (Alternative (..))
import Control.Arrow ((+++))
import Control.Monad (when)
import Control.Monad.Trans.Reader (ReaderT (runReaderT), asks, local)
import Data.Char (isAlphaNum, isLetter, isSpace)
import Data.Foldable (asum)
import Data.Functor (void, (<&>))
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import Data.Text (Text)
import qualified Data.Text as T
import Data.Void (Void)
import Language.Lambda.Syntax.LambdaPi
import Text.Megaparsec (Parsec, between, eof, errorBundlePretty, label, notFollowedBy, runParser, satisfy, takeWhileP, try, (<?>))
import Text.Megaparsec.Char (string)
import Text.Megaparsec.Char.Lexer (decimal, skipBlockCommentNested, skipLineComment)
import qualified Text.Megaparsec.Char.Lexer as L

type VarMap = HashMap Text Int

type Parser = ReaderT VarMap (Parsec Void Text)

binding :: Text -> Parser a -> Parser a
binding v = local (HM.insert v 0 . HM.map succ)

anonymousBind :: Parser a -> Parser a
anonymousBind = local $ HM.map succ

space :: Parser ()
space =
  L.space
    (void $ satisfy isSpace)
    (skipLineComment "--")
    (skipBlockCommentNested "{-" "-}")

keywords :: HS.HashSet Text
keywords = HS.fromList ["λ", "Π", "natElim", "0", "succ", "zero", "vecElim", "nil", "cons", "ℕ", "Nat", "Vec", "Type"]

isIdentHeadChar :: Char -> Bool
isIdentHeadChar = isLetter

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
      void $ string name <* notFollowedBy (satisfy isIdentBodyChar)

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
parens = between (symbol "(") (symbol ")")

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

lamAnnP :: Parser (Term 'Inferable)
lamAnnP = label "Typed lambda abstraction" $
  lexeme $
    try $ do
      reserved "λ"
      (bindee, typ) <-
        parens
          ( (,) <$> identifier
              <* symbol ":" <*> (termChkP <?> "variable type")
          )
          <* symbol "."
      binding bindee $ LamAnn typ <$> termInfP

piP :: Parser (Term 'Inferable)
piP = label "Pi-binding" $ do
  reserved "Π"
  (bindee, typ) <- parens $ (,) <$> identifier <*> termChkP
  binding bindee $ Pi typ <$> termChkP

eliminatorsP :: Parser (Term 'Inferable)
eliminatorsP =
  natElim' <$ reserved "natElim"
    <|> vecElim' <$ reserved "vecElim"

compoundTyConP :: Parser (Term 'Inferable)
compoundTyConP = vecCon' <$ reserved "Vec"

datConP :: Parser (Term 'Inferable)
datConP =
  naturalP
    <|> LamAnn Star' (Nil (Bound' 0)) <$ reserved "nil"
    <|> LamAnn Nat' (Succ (Bound' 0)) <$ reserved "succ"
    <|> cons' <$ reserved "cons"

sigP :: Parser (Term 'Inferable)
sigP =
  lexeme $ try $ (:::) <$> termChkP <* symbol ":" <*> termChkP

appP :: Parser (Term 'Inferable)
appP =
  (:@:) <$> termInfP <*> (Inf <$> termInfP)

termInfP :: Parser (Term 'Inferable)
termInfP = termInfPrecP 0

naturalP :: ReaderT VarMap (Parsec Void Text) (Term 'Inferable)
naturalP =
  lexeme decimal <&> \n ->
    foldr ($) Zero (replicate n (Succ . Inf))

termInfPrecP :: Int -> Parser (Term 'Inferable)
termInfPrecP 0 =
  -- Processes Pi-constructs and annotated lambdas
  piP <|> lamAnnP
    <|> (handleTrailingArrow =<< termInfPrecP 1)
  where
    handleTrailingArrow t =
      try (Pi (Inf t) <$ symbol "->" <*> anonymousBind (termChkPrecP 0))
        <|> pure t
termInfPrecP 1 =
  -- Processes type annotations
  asum
    [ do
        t <- termInfPrecP 2
        try (parseSig $ Inf t) <|> pure t
    , parseSig =<< parens unAnnLamP
    ]
termInfPrecP 2 =
  foldl (:@:) <$> termInfPrecP 3 <*> many (termChkPrecP 3)
termInfPrecP _ =
  primTypeP
    <|> compoundTyConP
    <|> datConP
    <|> eliminatorsP
    <|> varP
    <|> parens (termInfPrecP 0)

parseSig :: Term 'Checkable -> Parser (Term 'Inferable)
parseSig e =
  (e :::) <$ symbol ":" <*> termChkPrecP 0

termChkPrecP :: Int -> Parser (Term 'Checkable)
termChkPrecP 0 = unAnnLamP <|> Inf <$> termInfPrecP 0
termChkPrecP d =
  try (parens unAnnLamP) <|> Inf <$> termInfPrecP d

termChkP :: Parser (Term 'Checkable)
termChkP =
  label "checkable terms" $
    try (parens unAnnLamP) <|> unAnnLamP <|> Inf <$> termInfP

unAnnLamP :: Parser (Term 'Checkable)
unAnnLamP = label "Unannotated lambda" $
  lexeme $
    try $ do
      reserved "λ"
      bindee <- identifier <?> "variable name"
      binding bindee $
        Lam <$ symbol "." <*> (termChkP <?> "lambda body")

parseOnly ::
  Parser a ->
  Text ->
  Either String a
parseOnly p = (errorBundlePretty +++ id) . runParser (runReaderT p mempty) "<input>"

lambdaExp :: Parser (Term 'Checkable)
lambdaExp = termChkP <* eof

-- >>> either error tryEval $ parseOnly (lambdaExp) "(λ(n : Nat). natElim (λ x. Nat) n (λ z. succ : Nat -> Nat : *)) 2 40"
-- Right (42,ℕ)
