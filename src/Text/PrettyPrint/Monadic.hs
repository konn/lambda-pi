{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Text.PrettyPrint.Monadic (
  Pretty (..),
  render,
  renderStyle,
  DocM (..),
  Doc,
  Style (..),
  execDocM,

  -- * Constructing documents

  -- ** Converting values into documents
  char,
  string,
  text,
  sizedText,
  zeroWidthText,
  int,
  integer,
  float,
  double,
  rational,

  -- ** Simpe dervied documents
  semi,
  comma,
  colon,
  space,
  equals,
  lparen,
  rparen,
  lbrack,
  rbrack,
  lbrace,
  rbrace,

  -- ** Wrapping documents in delimiters
  appWhen,
  parens,
  brackets,
  braces,
  quotes,
  doubleQuotes,

  -- ** Combining Documents
  mempty,
  (<>),
  (<+>),
  hcat,
  hsep,
  ($$),
  ($+$),
  vcat,
  sep,
  cat,
  fsep,
  fcat,
  nest,
  hang,
  punctuate,

  -- ** Precedence treatment
  withPrecParens,
  withPrecedence,

  -- * Other
  isolated,
  censorDoc,
) where

import Control.Lens
import Control.Monad ((<=<))
import Control.Monad.Morph
import Control.Monad.Reader.Class
import Control.Monad.Trans.Reader (ReaderT (..))
import Control.Monad.Trans.Writer.CPS
import Data.Generics.Labels ()
import Data.List.NonEmpty.Utils qualified as NE
import Data.Monoid
import Data.String
import Data.Text qualified as T
import Data.Text.Lazy qualified as LT
import GHC.Generics
import Text.PrettyPrint (Doc, Style)
import Text.PrettyPrint qualified as PP

execDocM :: e -> DocM e () -> Doc
execDocM pe (DocM act) = execWriter $ runReaderT act (PrettyEnv 0 pe)

newtype DocM e a = DocM {runDocM :: ReaderT (PrettyEnv e) (Writer Doc) a}
  deriving (Semigroup, Monoid) via Ap (ReaderT (PrettyEnv e) (Writer Doc)) a
  deriving newtype (Functor, Applicative, Monad)

instance MonadReader e (DocM e) where
  ask = DocM $ asks env
  {-# INLINE ask #-}
  local f (DocM act) = DocM $ local (#env %~ f) act
  {-# INLINE local #-}

instance a ~ () => IsString (DocM e a) where
  fromString = DocM . lift . tell . fromString

type Precedence = Int

data PrettyEnv e = PrettyEnv {precedence :: !Precedence, env :: !e}
  deriving (Show, Eq, Ord, Generic, Functor, Foldable, Traversable)

parens, brackets, braces, quotes, doubleQuotes :: DocM e a -> DocM e a
{-# INLINE parens #-}
parens = censorDoc PP.parens
{-# INLINE brackets #-}
brackets = censorDoc PP.brackets
{-# INLINE braces #-}
braces = censorDoc PP.braces
{-# INLINE quotes #-}
quotes = censorDoc PP.quotes
{-# INLINE doubleQuotes #-}
doubleQuotes = censorDoc PP.doubleQuotes

censorDoc :: (Doc -> Doc) -> DocM e a -> DocM e a
{-# INLINE censorDoc #-}
censorDoc f = DocM . hoist (censor f) . runDocM

infixl 6 <+>

(<+>) :: DocM e () -> DocM e () -> DocM e ()
p <+> q = do
  l <- isolated p
  r <- isolated q
  putDoc $ l PP.<+> r

infixl 5 $$, $+$

hcat :: [DocM e ()] -> DocM e ()
{-# INLINE hcat #-}
hcat = putDoc . PP.hcat <=< mapM isolated

hsep :: [DocM e ()] -> DocM e ()
{-# INLINE hsep #-}
hsep = putDoc . PP.sep <=< mapM isolated

($$) :: DocM e () -> DocM e () -> DocM e ()
p $$ q = do
  l <- isolated p
  r <- isolated q
  putDoc $ l PP.$$ r

($+$) :: DocM e () -> DocM e () -> DocM e ()
p $+$ q = do
  l <- isolated p
  r <- isolated q
  putDoc $ l PP.$+$ r

vcat :: [DocM e ()] -> DocM e ()
{-# INLINE vcat #-}
vcat = putDoc . PP.vcat <=< mapM isolated

sep :: [DocM e ()] -> DocM e ()
{-# INLINE sep #-}
sep = putDoc . PP.sep <=< mapM isolated

cat :: [DocM e ()] -> DocM e ()
{-# INLINE cat #-}
cat = putDoc . PP.cat <=< mapM isolated

fsep :: [DocM e ()] -> DocM e ()
{-# INLINE fsep #-}
fsep = putDoc . PP.fsep <=< mapM isolated

fcat :: [DocM e ()] -> DocM e ()
{-# INLINE fcat #-}
fcat = putDoc . PP.fcat <=< mapM isolated

nest :: Int -> DocM e a -> DocM e a
{-# INLINE nest #-}
nest = censorDoc . PP.nest

hang :: DocM e () -> Int -> DocM e () -> DocM e ()
{-# INLINE hang #-}
hang l d r = do
  ld <- isolated l
  rd <- isolated r
  putDoc $ PP.hang ld d rd

punctuate :: DocM e () -> [DocM e a] -> [DocM e a]
punctuate s ds =
  case NE.unsnoc <$> NE.nonEmpty ds of
    Nothing -> []
    Just ([], a) -> [a]
    Just (as, a) -> map (<* s) as ++ [a]

putDoc :: Doc -> DocM e ()
{-# INLINE putDoc #-}
putDoc = DocM . lift . tell

char :: Char -> DocM e ()
{-# INLINE char #-}
char = putDoc . PP.char

string :: String -> DocM e ()
{-# INLINE string #-}
string = putDoc . PP.text

text :: T.Text -> DocM e ()
{-# INLINE text #-}
text = putDoc . PP.text . T.unpack

sizedText :: Int -> String -> DocM e ()
{-# INLINE sizedText #-}
sizedText n = putDoc . PP.sizedText n

zeroWidthText :: String -> DocM e ()
{-# INLINE zeroWidthText #-}
zeroWidthText = putDoc . PP.zeroWidthText

int :: Int -> DocM e ()
{-# INLINE int #-}
int = putDoc . PP.int

integer :: Integer -> DocM e ()
{-# INLINE integer #-}
integer = putDoc . PP.integer

float :: Float -> DocM e ()
{-# INLINE float #-}
float = putDoc . PP.float

double :: Double -> DocM e ()
{-# INLINE double #-}
double = putDoc . PP.double

rational :: Rational -> DocM e ()
{-# INLINE rational #-}
rational = putDoc . PP.rational

semi
  , comma
  , colon
  , space
  , equals
  , lparen
  , rparen
  , lbrack
  , rbrack
  , lbrace
  , rbrace ::
    DocM e ()
{-# INLINE semi #-}
semi = putDoc PP.semi
{-# INLINE comma #-}
comma = putDoc PP.comma
{-# INLINE colon #-}
colon = putDoc PP.colon
{-# INLINE space #-}
space = putDoc PP.space
{-# INLINE equals #-}
equals = putDoc PP.equals
{-# INLINE lparen #-}
lparen = putDoc PP.lparen
{-# INLINE rparen #-}
rparen = putDoc PP.rparen
{-# INLINE lbrack #-}
lbrack = putDoc PP.lbrack
{-# INLINE rbrack #-}
rbrack = putDoc PP.rbrack
{-# INLINE lbrace #-}
lbrace = putDoc PP.lbrace
{-# INLINE rbrace #-}
rbrace = putDoc PP.rbrace

{- |
Runs DocM computation in isolated env and returns underlying 'Doc'
/WITHOUT/ 'tell'ing the result.
-}
isolated :: DocM e () -> DocM e Doc
isolated (DocM act) = do
  e <- DocM ask
  execWriterT $ flip runReaderT e $ hoist (mapWriterT generalize) act

withPrecedence :: Precedence -> DocM e a -> DocM e a
withPrecedence p = DocM . local (#precedence .~ p) . runDocM

-- | Encloses with parens if the current precedence is greater than the first argument.
withPrecParens :: Precedence -> DocM e a -> DocM e a
{-# INLINE withPrecParens #-}
withPrecParens d0 act = do
  d <- DocM $ asks precedence
  withPrecedence d0 $
    if d <= d0 then act else parens act

class Pretty e a where
  pretty :: a -> DocM e ()

instance Pretty e Int where
  pretty = int

instance Pretty e Integer where
  pretty = integer

instance Pretty e Float where
  pretty = float

instance Pretty e Double where
  pretty = double

instance Pretty e Rational where
  pretty = rational

instance Pretty e T.Text where
  pretty = fromString . T.unpack

instance Pretty e LT.Text where
  pretty = fromString . LT.unpack

instance Pretty e String where
  pretty = fromString

renderStyle :: Style -> e -> DocM e () -> String
renderStyle sty e = PP.renderStyle sty . execDocM e

render :: e -> DocM e () -> String
render = renderStyle PP.style

appWhen :: Bool -> (m a -> m a) -> m a -> m a
appWhen True = ($)
appWhen False = const id
