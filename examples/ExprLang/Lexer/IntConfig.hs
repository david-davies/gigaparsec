{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}


module ExprLang.Lexer.IntConfig (
  uIntCfg,
  sIntCfg
  ) where


import Text.Gigaparsec.Token.Descriptions qualified as Desc
import Text.Gigaparsec.Token.Lexer qualified as Lexer

import Data.Int (Int64)

import Text.Gigaparsec.Token.Patterns

import Data.Word (Word8, Word32)
import Data.Int  (Int8, Int16, Int32)
import Text.Gigaparsec.Internal.Token.BitBounds (Bits(..))



uIntCfg :: IntegerParserConfig
uIntCfg = emptyUnsignedIntegerParserConfig {
    prefix = "u",
    widths = [(B8, [t| Word8 |]), (B32, [t| Word32 |])],
    bases = [Hexadecimal, Decimal, Binary],
    includeUnbounded = False,
    signedOrUnsigned = Unsigned,
    collatedParser = Just "natural"
  }

sIntCfg :: IntegerParserConfig
sIntCfg = emptySignedIntegerParserConfig {
    prefix = "s",
    widths = [(B64, [t| Integer |])],
    bases = [Hexadecimal],
    includeUnbounded = True,
    signedOrUnsigned = Signed,
    collatedParser = Just "integer"
  }