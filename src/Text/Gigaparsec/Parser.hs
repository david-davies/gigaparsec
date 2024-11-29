{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE UndecidableInstances #-}
module Text.Gigaparsec.Parser 
  (Parser(..))
  where

import Data.Kind (Constraint)
import Control.Selective (Selective (..))
import Control.Applicative (Alternative)
import Text.Gigaparsec.Internal (Parsec)
import Data.Set (Set)
import Control.Monad.Trans.Class (MonadTrans (lift))
import GHC.Base (Alternative(..))
import Control.Monad.Trans.Except (catchE)


type Parser :: (* -> *) -> Constraint
class (Monad parser, Alternative parser, Selective parser) => Parser parser where
  atomic :: parser a -> parser a
  lookAhead :: parser a -> parser a
  notFollowedBy :: parser a -> parser ()
  eof :: parser ()
  satisfy :: (Char -> Bool) -> parser Char
  string :: String -> parser String
  label :: Set String -> parser a -> parser a

  unit :: parser ()
  unit = pure ()

  infixl 4 <~>
  (<~>) :: parser a      -- ^ @p@, the first parser to run.
        -> parser b      -- ^ @q@, the second parser to run.
        -> parser (a, b) -- ^ a parser that runs @p@ and then @q@, and pairs their results.
  (<~>) = liftA2 (,)

  infixl 4 $>
  ($>) :: parser a -- ^ @p@, the parser to run, whose result is ignored.
       -> b        -- ^ @x@, the value to return
       -> parser b -- ^ a parser that runs @p@, but returns the value @x@.
  ($>) = flip (<$)

instance (MonadTrans t, Parser p) => Alternative (t p) where
  empty :: t p a
  empty = lift empty
  -- ! TODO This does not look like it satisfies the right laws.
  -- I think we need the user to supply this. 
  -- or perhaps need some smaller typeclass of things that have two types of error:
  -- one consuming input, and one not
  (<|>) :: forall a . t p a -> t p a -> t p a
  (<|>) f g = 
      let foo :: t p a -> t p a -> t p a = _ -- lift (<|>) 
          bar :: t ((->) (p a)) (p a -> p a) = lift @t (<|>)
          baz :: t ((->) (p a)) (p a -> p a) = lift (<|>)
          foo2 = liftA2 _ f g
      in  do
        x <- f
        _
        -- liftA2 baz f g
instance (MonadTrans t, Parser p) => Selective (t p) where
  {-# INLINE select #-}
  select :: t p (Either a b) -> t p (a -> b) -> t p b
  select e f = do
    x <- e
    case x of
      Left a -> lift . pure . ($ a) =<< f
      Right b -> pure b
{-| User will need to supply an `Alternative` instance,
as there is no way to define `(<|>)`, without knowing more about the transformer `t`.

Imagine we were trying to define this,

> (<|>) :: t p a -> t p a -> t p a
> (<|>) f g = ...



-}
instance (MonadTrans t, Parser p, Alternative (t p)) => Parser (t p) where


instance Parser Parsec where
instance (Semigroup m, Parser p) => Semigroup (p m) where
  {-# INLINE (<>) #-}
  (<>) :: p m -> p m -> p m
  (<>) = liftA2 (<>)
instance (Monoid m, Parser p) => Monoid (p m) where
  {-# INLINE mempty #-}
  mempty :: p m
  mempty = pure mempty


  