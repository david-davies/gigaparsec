{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE TemplateHaskell, TypeOperators, CPP, UnicodeSyntax, ExistentialQuantification #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-unused-do-bind #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleInstances #-}
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
import Text.Gigaparsec.Token.Lexer (Lexer (space), lexeme, sym, Symbol, symbol, Lexeme (names, integer, natural, charLiteral), Space, Names, CanHoldSigned, CanHoldUnsigned)

import Text.Gigaparsec.Internal.Patterns (sanitiseBndrStars, sanitiseTypeStars)

import Data.String (IsString(fromString))
import Language.Haskell.TH.Syntax (Q, Dec (..), Exp (VarE), Name (Name), OccName (OccName), reifyType, Type (ForallT), Quasi (qRecover), reifyInstances, reify, Quote (newName), nameBase, Body (..), Code, unTypeCode, isInstance, runIO, mkName, Inline (Inline), Phases (AllPhases))

import Language.Haskell.TH (Type(MulArrowT), Pat (VarP), sigD, pprint, RuleMatch (FunLike))

import Language.Haskell.TH (Type (..), funD, clause, normalB, varE, Ppr (ppr), pragInlD)
import Control.Arrow (Arrow(first))
import Control.Monad (when, guard, unless)
import Control.Applicative (Alternative)
import Data.Kind (Constraint)
import Debug.Trace (trace)
import Text.Gigaparsec.Internal.Token.Numeric (IntegerParsers)
import Text.Gigaparsec.Internal.Token.Text (TextParsers)

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


{-|
Generate the given lexer combinators from a given lexer.
-}
lexerCombinators
  :: Code Q Lexer -- The lexer
  -> [Name] -- The combinators to generate
  -> Q [Dec]
lexerCombinators lexer = fmap concat . traverse mkCombinator
  where
    mkCombinator :: Name -> Q [Dec]
    mkCombinator x = do
      tp <- reifyType x
      (prefix, dom, _, cod) <-
        fail (notFunctionTypeMsg x tp) `qRecover` fnTpDomain tp
      let newTp = prefix cod
      (`unless` fail (notLexerFieldMsg x dom)) =<< isInstance ''LexerField [dom]
      mkDec x newTp

    mkDec
      :: Name -- The name of the combinator
      -> Type -- The return type of the combinator to be formed
      -> Q [Dec]
    mkDec cName tp = do
      x <- newName (nameBase cName)
      sequence
        [ pragInlD x Inline FunLike AllPhases
        , sigD x (pure tp)
        , funD x [clause [] (normalB [| project $(varE cName) $(unTypeCode lexer) |]) []]
        ]

    notLexerFieldMsg :: Name -> Type -> String
    notLexerFieldMsg x tp = concat [
        "The function ", pprint x, " is not a valid lexer combinator.",
        "\n Cannot construct a combinator from its type `", pprint tp, "`."
      ]

    notFunctionTypeMsg :: Name -> Type -> String
    notFunctionTypeMsg x tp = concat ["Type of `", show x,"` is not a function type: ", show tp]

{-|
Denote the type of an arrow; it is either normal or linear.
-}
type ArrowTp :: *
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
fnTpDomain x = do
  (a, (b,c,d)) <- fnTpDomain' x
  (a,,c,) <$> sanitiseTypeStars b <*> sanitiseTypeStars d
  where
  fnTpDomain' (ForallT bnds ctx tp) = do
    bnds' <- sanitiseBndrStars bnds
    first (ForallT bnds' ctx .) <$> fnTpDomain' tp
  fnTpDomain' (ForallVisT bnds tp) = do
    bnds' <- sanitiseBndrStars bnds
    first (ForallVisT bnds' .) <$> fnTpDomain' tp
  fnTpDomain' (AppT (AppT ArrowT a) b) =
    return (id, (a, StdArrow, b))

  fnTpDomain' (AppT (AppT MulArrowT a) b) =
    return (id, (a, LinearArrow, b))

  fnTpDomain' tp = fail
    ("Type of given function is not a function type: " ++ show tp)

---------------------------------------------------------------------------------------------------
-- Lexer Field

{-|
@a@ is a `LexerField` when it is the type of a component or subcomponent of the `Lexer` type.
This includes things like `Lexeme` and `Symbol`.
-}
type LexerField :: * -> Constraint
class LexerField a where
  project :: (a -> b) -> (Lexer -> b)

instance LexerField Lexer where
  {-# INLINE project #-}
  project :: (Lexer -> b) -> (Lexer -> b)
  project = id

---------------------------------------------------------------------------------------------------
-- Lexemes

instance LexerField Lexeme where
  {-# INLINE project #-}
  project :: (Lexeme -> b) -> (Lexer -> b)
  project f = f . lexeme

instance LexerField Symbol where
  {-# INLINE project #-}
  project :: (Symbol -> b) -> (Lexer -> b)
  project f = f . symbol . lexeme

instance LexerField Names where
  {-# INLINE project #-}
  project :: (Names -> b) -> (Lexer -> b)
  project f = f . names . lexeme

instance LexerField (IntegerParsers CanHoldSigned) where
  {-# INLINE project #-}
  project :: (IntegerParsers CanHoldSigned -> b) -> (Lexer -> b)
  project f = f . integer . lexeme

instance LexerField (IntegerParsers CanHoldUnsigned) where
  {-# INLINE project #-}
  project :: (IntegerParsers CanHoldUnsigned -> b) -> (Lexer -> b)
  project f = f . natural . lexeme

instance LexerField (TextParsers Char) where
  {-# INLINE project #-}
  project :: (TextParsers Char -> b) -> (Lexer -> b)
  project f = f . charLiteral . lexeme


---------------------------------------------------------------------------------------------------
-- Space

instance LexerField Space where
  {-# INLINE project #-}
  project :: (Space -> b) -> (Lexer -> b)
  project f = f . space

type IsLexer :: * -> Constraint
class IsLexer l where
  -- We never need this function, but it is good to have it as 
  -- it forces any instance to show how to construct a lexer
  toLexer :: l -> Lexer

instance IsLexer Lexer where
  {-# INLINE toLexer #-}
  toLexer :: Lexer -> Lexer
  toLexer = id
