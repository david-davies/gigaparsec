{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE TemplateHaskell #-}

{-# OPTIONS_GHC -Wno-missing-import-lists #-}

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
  lexerCombinatorsWithNames,
  -- * Integer Parsers
  generateIntegerParsers,
  -- ** IntegerParserConfig
  IntegerParserConfig,
  prefix, widths, bases, includeUnbounded, signedOrUnsigned, collatedParser,
  -- *** Presets
  emptyIntegerParserConfig,
  emptySignedIntegerParserConfig,
  emptyUnsignedIntegerParserConfig,
  -- *** Associated Types
  SignedOrUnsigned(..),
  IntLitBases(..),
  IntLitBase(..),
  ) where

import Text.Gigaparsec (Parsec)
import safe Text.Gigaparsec.Internal.Token.Lexer
    ( Lexeme(sym),
      Lexer(lexeme) )
import safe Text.Gigaparsec.Internal.Token.Patterns.IntegerParsers
    ( IntegerParserConfig(collatedParser, prefix, widths, bases,
                          includeUnbounded, signedOrUnsigned),
      SignedOrUnsigned(..),
      IntLitBases(..),
      IntLitBase(..),
      generateIntegerParsers,
      emptyIntegerParserConfig,
      emptySignedIntegerParserConfig,
      emptyUnsignedIntegerParserConfig )


import Data.String (IsString(fromString))
import Language.Haskell.TH.Syntax (Q, Dec (..), Exp)




import Text.Gigaparsec.Internal.Token.Patterns.LexerCombinators (lexerCombinators, lexerCombinatorsWithNames)

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

