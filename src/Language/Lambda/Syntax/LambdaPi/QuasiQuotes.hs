module Language.Lambda.Syntax.LambdaPi.QuasiQuotes (
  parsed,
  renamed,
) where

import Data.Data (Data)
import Data.String (IsString (..))
import Language.Haskell.TH
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Syntax (liftData)
import Language.Lambda.Syntax.LambdaPi.Parser
import Language.Lambda.Syntax.LambdaPi.Rename

parsed :: QuasiQuoter
parsed = mkQuoter exprP

renamed :: QuasiQuoter
renamed = mkQuoter $ renameExpr <$> exprP

mkQuoter :: Data a => Parser a -> QuasiQuoter
mkQuoter p =
  QuasiQuoter
    { quoteDec = error "No Dec Quoter"
    , quoteType = error "No Type Quoter"
    , quoteExp = \src -> do
        loc <- location
        case parseNamed (show loc) p $ fromString src of
          Right a -> liftData a
          Left err -> fail err
    , quotePat = error "No Pattern Quoter"
    }
