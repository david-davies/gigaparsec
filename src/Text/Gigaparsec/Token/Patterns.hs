{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE TemplateHaskell, TypeOperators, CPP, UnicodeSyntax, ExistentialQuantification #-}
{-|
Module      : Text.Gigaparsec.Token.Patterns
Description : Template Haskell generators to help with patterns
License     : BSD-3-Clause
Maintainer  : Jamie Willis, Gigaparsec Maintainers
Stability   : experimental

This module is currently experimental, and may have bugs depending on the version
of Haskell, or the extensions enabled. Please report any issues to the maintainers.

@since 0.2.2.0
-}
module Text.Gigaparsec.Token.Patterns (
  overloadedStrings,
  lexerCombinators,
  ) where

import Text.Gigaparsec (Parsec)
import Text.Gigaparsec.Token.Lexer (Lexer, lexeme, sym, Symbol, symbol, Lexeme)

import Data.String (IsString(fromString))
import Language.Haskell.TH.Syntax (Q, Dec (..), Exp (VarE), Name (Name), OccName (OccName), reifyType, Type (ForallT), Quasi (qRecover), reifyInstances, reify, Quote (newName), nameBase, Body (..), Code)
#if __GLASGOW_HASKELL__ >= 902
import Language.Haskell.TH (Type(MulArrowT), Pat (VarP))
#endif
import Language.Haskell.TH (Type (..))
import Control.Arrow (Arrow(first))
import Control.Monad (when, guard)
import Control.Applicative (Alternative)
import Data.Kind (Constraint)

{-|
When given a quoted reference to a 'Text.Gigaparsec.Token.Lexer.Lexer', for example
@[|lexer|]@, this function will synthesise an `IsString` instance that will
allow string literals to serve as @Parsec ()@. These literals will parse symbols
in the language associated with the lexer, followed by consuming valid whitespace.

@since 0.2.2.0
-}
overloadedStrings :: Q Exp   -- ^ the quoted 'Text.Gigaparsec.Token.Lexer.Lexer'
                  -> Q [Dec] -- ^ a synthesised `IsString` instance.
overloadedStrings qlexer = [d|
    instance u ~ () => IsString (Parsec u) where
      fromString = sym (lexeme $qlexer) -- TODO: one day, $qlexer.lexeme.sym
  |]

guardM :: (Alternative m, Monad m) => m Bool -> m a -> m a
guardM cond a = do
  b <- cond
  guard b
  a

type LexerField :: * -> Constraint
class LexerField a where
  project :: (a -> b) -> (Lexer -> b)

instance LexerField Lexeme where
  {-# INLINE project #-}
  project :: (Lexeme -> b) -> (Lexer -> b)
  project f = f . lexeme

instance LexerField Symbol where
  {-# INLINE project #-}
  project :: (Symbol -> b) -> (Lexer -> b)
  project f = f . symbol . lexeme


data LexerComponent = ∀ a b . LexerField a => LC (a -> b)

foo :: LexerComponent
foo = LC (symbol)

comb2 :: Lexer -> Name -> LexerComponent -> Q [Dec]
comb2 l n (LC f) = do
  x <- newName (nameBase n)
  let y = project f l
  -- [d| $(pure $ VarP x) = y |]
  return [ValD (VarP x) (NormalB [|y|]) []]
  -- [d| $x = project f l |]

{-|
Generate the given lexer combinators from a given lexer.
-}
lexerCombinators 
  :: Lexer
  -> [Name]
  -> Q [Dec]
lexerCombinators lexer ns = traverse mkCombinator ns
  where
    nmToFunc :: Name -> Exp
    nmToFunc = VarE
    mkCombinator :: Name -> Q Dec
    mkCombinator x = do
      tm <- reify x
      tp <- reifyType x
      (prefix, dom, arrTp, cod) <- (fail $ concat ["Type of `", show x,"` is not a function type: ", show tp]) 
          `qRecover` 
        (fnTpDomain tp)
      reifyInstances ''LexerField []
      _

    getLexerProjection :: Type -> Q Exp
    getLexerProjection tp = do
      is <- reifyInstances ''LexerField [tp]
      case is of
        -- Is it fine to have more than one instance for `tp`?
        i: _ -> _
        [] -> fail $ concat ["No instances"]

    projectFromLexer :: Type -> Q Exp
    projectFromLexer tp = do
      -- t <- [t| Lexer |]
      -- guardM (t == tp)
      _
    -- mkSymbolCombinator
    -- Use nameBase
    -- getNameStem :: Name -> String
    -- getNameStem (Name (OccName x) _) = x
    -- getNameStem n = error $ concat [
    --     "lexerCombinators: ",
    --     "The given name `", show n,
    --     "` is not a qualified import of a lexer function"
    --   ]

{-|
Denote the type of an arrow; it is either normal or linear.
-}
data ArrowTp = StdArrow | LinearArrow

{-|
Get the domain of a function type.
Keep any prefixed constraints and type variable quantifiers as a prefixing function.
-}
fnTpDomain 
      :: Type 
      ->  Q (Type -> Type, Type, ArrowTp, Type) 
          -- The head of the type, includes any preceding constraints 
          -- and foralls. this is a function which prefixes the given type with the constraints/foralls
          -- The domain and codomain of the type
fnTpDomain = ((\(a, (b,c,d)) -> (a,b,c,d)) <$>) . fnTpDomain' 
  where
  fnTpDomain' (ForallT bnds ctx tp) =
    first (ForallT bnds ctx .) <$> fnTpDomain' tp
  fnTpDomain' (ForallVisT bnds tp) = 
    first (ForallVisT bnds .) <$> fnTpDomain' tp
  fnTpDomain' (AppT (AppT ArrowT a) b) = 
    return (id, (a, StdArrow, b))
#if __GLASGOW_HASKELL__ >= 902
  fnTpDomain' (AppT (AppT MulArrowT a) b) = 
    return (id, (a, LinearArrow, b))
#endif
  fnTpDomain' tp = fail 
    ("Type of given function is not a function type: " ++ show tp)
