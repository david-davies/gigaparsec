{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}

{- |
This module describes the Lexer for @ExprLang@.
This lexer description need not be exposed to the other modules, so instead we
expose some primitive 'lexing' combinators defined in terms of a lexer description.
-}
module ExprLang.Lexer (
  keywords,
  operators,
  keyword,
  operator,
  integer,
  identifier,
  fully,
  alter,
  whiteSpace,
) where

import Text.Gigaparsec.Token.Descriptions qualified as Desc
import Text.Gigaparsec.Token.Lexer qualified as Lexer

import Data.Char (
  generalCategory,
  isAlpha,
  isAlphaNum,
  isSpace,
 )
import Data.Char qualified as Char (GeneralCategory (Space))
import Data.Int (Int64)
import Data.Set (Set)
import Text.Gigaparsec (Parsec, (<|>))
import Text.Gigaparsec.Token.Patterns (lexerCombinators, lexerCombinatorsWithNames, overloadedStrings, lexerUnsignedParsers)

-- | The reserved keywords of the language
keywords :: Set String
keywords = ["return"]

{- | The reserved operators of the language.

This includes the binary operators in expressions, as well as the assignment operator '='.
-}
operators :: Set String
operators = ["+", "*", "-", "/", "="]

{- |
The lexer generated from a lexical description, which provide an abstract way of turning input
into 'tokens'.

All other lexing combinators should be defined in terms of this.
-}
lexer :: Lexer.Lexer
lexer =
  Lexer.mkLexer $
    Desc.plain
      { Desc.nameDesc = nameDesc
      , Desc.symbolDesc = symbolDesc
      , Desc.numericDesc = numericDesc
      , Desc.textDesc = textDesc
      , Desc.spaceDesc = spaceDesc
      }
 where
  nameDesc =
    Desc.plainName
      { Desc.identifierStart = Just isAlpha
      , Desc.identifierLetter = Just isAlphaNum
      }
  symbolDesc =
    Desc.plainSymbol
      { Desc.hardKeywords = keywords
      , Desc.hardOperators = operators
      , Desc.caseSensitive = True
      }
  numericDesc = Desc.plainNumeric
  textDesc = Desc.plainText
  spaceDesc =
    Desc.plainSpace
      { Desc.lineCommentStart = "//"
      , Desc.lineCommentAllowsEOF = True
      , Desc.multiLineCommentStart = "/*"
      , Desc.multiLineCommentEnd = "*/"
      , Desc.multiLineNestedComments = False
      , Desc.space = Just ((Char.Space ==) . generalCategory)
      , Desc.whitespaceIsContextDependent = True
      }

{-| Generate the lexer combinators -}
$( lexerCombinators
    [|lexer|]
    ['Lexer.lexeme, 'Lexer.fully, 'Lexer.identifier, 'Lexer.stringLiteral]
 )

$( lexerCombinatorsWithNames
    [|lexer|]
    [ ('Lexer.softKeyword, "keyword")
    , ('Lexer.softOperator, "operator")
    , ('Lexer.alter, "alterPred")
    , ('Lexer.integer, "integerParsers")
    ]
 )

$( lexerUnsignedParsers [| lexer |] "u")

-- Generate the OverloadedStrings for the lexer.
$(overloadedStrings [|lexer|])


{- | Parses a single \'integer\' token.
This may be written in decimal, hexadecimal, or binary form.
-}
{-# INLINE integer #-}
integer :: Parsec Int64
integer =
        wrap Lexer.decimal64
    <|> wrap Lexer.hexadecimal64
    <|> wrap Lexer.binary64
 where
  -- Have to process the output as gigaparsec doesn't yet support `Int64` as a valid output
  -- type of the numeric processors of the lexer.
  {-# INLINE wrap #-}
  wrap p = fromInteger <$> p integerParsers

{- | Change how whitespace is parsed while running the given parser @p@.
The given predicate @pred@ will return 'True' for what characters are considered whitespace.
-}
{-# INLINE alter #-}
alter ::
  -- | @pred@, defines what characters are to be considered whitespace when running @p@.
  (Char -> Bool) ->
  -- | @p@, the parser to run with the altered definition of whitespace, according to @pred@.
  Parsec a ->
  -- | a parser that runs @p@ with the changed definition of whitespace.
  Parsec a
alter = alterPred . Just

{-# INLINE whiteSpace #-}
whiteSpace :: Parsec ()
whiteSpace = Lexer.whiteSpace (Lexer.space lexer)
