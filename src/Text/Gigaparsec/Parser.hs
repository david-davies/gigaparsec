{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Text.Gigaparsec.Parser (Parser (..))
where

import Text.Gigaparsec qualified as Parsec
import Text.Gigaparsec.Internal (Parsec)

import Control.Applicative (Alternative)
import Control.Selective (Selective)
import Data.Kind (Constraint)
import Data.Set (Set)
import Text.Gigaparsec.Char qualified as Parsec
import Text.Gigaparsec.Errors.Combinator qualified as Parsec

type Parser :: (* -> *) -> Constraint

{-# RULES 
"stage/toParsec" toParsec = toParsec'
"stage/fromParsec" fromParsec = fromParsec'
"toParsec/fromParsec" forall x . toParsec (fromParsec x) = x
"fromParsec/toParsec" forall x . fromParsec (toParsec x) = x
#-}


{-# NOINLINE[0] toParsec' #-}
toParsec' :: Parser p => p a -> Parsec a 
toParsec' = toParsec

{-# NOINLINE[0] fromParsec' #-}
fromParsec' :: Parser p => Parsec a -> p a
fromParsec' = fromParsec

class (Monad parser, Alternative parser, Selective parser) => Parser parser where
  toParsec   :: parser a -> Parsec a
  fromParsec :: Parsec a -> parser a

  {-# INLINE pipeToParsec #-}
  pipeToParsec :: (Parsec a -> Parsec b) -> parser a -> parser b
  pipeToParsec f = fromParsec . f . toParsec

  {-# INLINE atomic #-}
  atomic :: parser a -> parser a
  atomic = pipeToParsec Parsec.atomic

  {-# INLINE lookAhead #-}
  lookAhead :: parser a -> parser a
  lookAhead = pipeToParsec Parsec.lookAhead

  {-# INLINE notFollowedBy #-}
  notFollowedBy :: parser a -> parser ()
  notFollowedBy = pipeToParsec Parsec.notFollowedBy

  {-# INLINE eof #-}
  eof :: parser ()
  eof = fromParsec Parsec.eof

  {-# INLINE satisfy #-}
  satisfy :: (Char -> Bool) -> parser Char
  satisfy = fromParsec . Parsec.satisfy

  {-# INLINE string #-}
  string :: String -> parser String
  string = fromParsec . Parsec.string

  {-# INLINE label #-}
  label :: Set String -> parser a -> parser a
  label = pipeToParsec . Parsec.label

  {-# INLINE unit #-}
  unit :: parser ()
  unit = pure ()

  infixl 4 <~>
  (<~>)
    :: parser a
    -- ^ @p@, the first parser to run.
    -> parser b
    -- ^ @q@, the second parser to run.
    -> parser (a, b)
    -- ^ a parser that runs @p@ and then @q@, and pairs their results.
  (<~>) = liftA2 (,)

  infixl 4 $>
  ($>)
    :: parser a
    -- ^ @p@, the parser to run, whose result is ignored.
    -> b
    -- ^ @x@, the value to return
    -> parser b
    -- ^ a parser that runs @p@, but returns the value @x@.
  ($>) = flip (<$)

instance Parser Parsec where
  {-# INLINE fromParsec #-}
  fromParsec :: Parsec a -> Parsec a
  fromParsec = id
  {-# INLINE toParsec #-}
  toParsec :: Parsec a -> Parsec a
  toParsec = id
  
instance (Semigroup m, Parser p) => Semigroup (p m) where
  {-# INLINE (<>) #-}
  (<>) :: p m -> p m -> p m
  (<>) = liftA2 (<>)
instance (Monoid m, Parser p) => Monoid (p m) where
  {-# INLINE mempty #-}
  mempty :: p m
  mempty = pure mempty
