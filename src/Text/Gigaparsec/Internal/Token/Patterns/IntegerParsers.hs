{-# LANGUAGE Trustworthy #-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-missing-import-lists #-}

module Text.Gigaparsec.Internal.Token.Patterns.IntegerParsers (
  module Text.Gigaparsec.Internal.Token.Patterns.IntegerParsers
) where

import Text.Gigaparsec (Parsec)
import Text.Gigaparsec.Internal.Token.Lexer (natural, integer)

import Language.Haskell.TH.Syntax (Dec (..), Exp, Inline (Inline), Phases (AllPhases), Q, Quote (newName), Type, nameBase)

import Control.Monad (forM)
import Data.Bitraversable (bisequence)
import Data.Function (on)
import Data.List (groupBy)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (fromJust)
import Data.Set (Set)
import Data.Set qualified as Set
import Language.Haskell.TH (
  RuleMatch (FunLike),
  pragInlD,
  sigD,
  varE,
 )
import Text.Gigaparsec.Internal.TH.VersionAgnostic (Name)
import Text.Gigaparsec.Internal.Token.BitBounds (Bits (..))
import Text.Gigaparsec.Token.Lexer qualified as Lexer

import GHC.Exts (IsList (..))
import Text.Gigaparsec.Internal.TH.DecUtils (funDsingleClause)
import Text.Gigaparsec.Internal.Token.Patterns.LexerCombinators

intLitBaseList :: [IntLitBase]
intLitBaseList = [Binary, Octal, Decimal, Hexadecimal]

-- | Names of the
integerParsers :: [(Name, IntLitBase)]
integerParsers =
  [ 'Lexer.binary
  , 'Lexer.octal
  , 'Lexer.decimal
  , 'Lexer.hexadecimal
  ]
    `zip` intLitBaseList

intParsers8Bit :: [(Name, IntLitBase)]
intParsers8Bit =
  [ 'Lexer.binary8
  , 'Lexer.octal8
  , 'Lexer.decimal8
  , 'Lexer.hexadecimal8
  ]
    `zip` intLitBaseList

intParsers16Bit :: [(Name, IntLitBase)]
intParsers16Bit =
  [ 'Lexer.binary16
  , 'Lexer.octal16
  , 'Lexer.decimal16
  , 'Lexer.hexadecimal16
  ]
    `zip` intLitBaseList

intParsers32Bit :: [(Name, IntLitBase)]
intParsers32Bit =
  [ 'Lexer.binary32
  , 'Lexer.octal32
  , 'Lexer.decimal32
  , 'Lexer.hexadecimal32
  ]
    `zip` intLitBaseList

intParsers64Bit :: [(Name, IntLitBase)]
intParsers64Bit =
  [ 'Lexer.binary64
  , 'Lexer.octal64
  , 'Lexer.decimal64
  , 'Lexer.hexadecimal64
  ]
    `zip` intLitBaseList

type IntLitBase :: *
data IntLitBase
  = Binary
  | Octal
  | Decimal
  | Hexadecimal
  deriving stock (Show, Eq, Ord)

type IntLitBases :: *
data IntLitBases
  = AllBases
  | IntLitBases (Set IntLitBase)

instance IsList IntLitBases where
  type Item IntLitBases = IntLitBase
  fromList = IntLitBases . fromList
  toList AllBases = intLitBaseList
  toList (IntLitBases xs) = Set.toList xs

type SignedOrUnsigned :: *
data SignedOrUnsigned
  = Signed
  | Unsigned

isSigned :: SignedOrUnsigned -> Bool
isSigned Signed = True
isSigned Unsigned = False

type IntegerParserConfig :: *
data IntegerParserConfig = IntegerParserConfig
  { prefix :: String
  -- ^
  --     The string to prepend to each generated parser's name (except for the `collatedParser`, if specified).
  , widths :: Map Bits (Q Type)
  -- ^
  --     The fixed bit-widths (8-bit, 16-bit, etc/) for which to generate parsers.
  , bases :: IntLitBases
  -- ^
  --     The numeric bases (binary, octal, etc) for which to generate parsers.
  , includeUnbounded :: Bool
  -- ^
  --     When 'True', generate the unbounded integer parsers for each base specified in `bases`.
  , collatedParser :: Maybe String
  -- ^
  --     Generate a generic integer parser with the given name,
  --     at each width (including unbounded) specified by `widths`, that
  --     is able to parse each base specified in `bases`.
  --
  --     * If 'Nothing', do not generate such a parser.
  --     * If @'Just' ""@, then the default name will be @"natural"@  or @"integer"@ when `signedOrUnsigned`
  --       is `Unsigned` or `Signed`, respectively.
  , signedOrUnsigned :: SignedOrUnsigned
  -- ^
  --     Whether or not the parsers to generate are for 'Signed' or 'Unsigned' integers.
  }

filterByBase :: IntLitBases -> [(a, IntLitBase)] -> [a]
filterByBase AllBases = map fst
filterByBase (IntLitBases bs) = map fst . filter ((`Set.member` bs) . snd)

filterByWidth :: Bits -> [(Bits, a)] -> [a]
filterByWidth b = map snd . filter ((== b) . fst)

mwhen :: (Monoid m) => Bool -> m -> m
mwhen True x = x
mwhen False _ = mempty

groupByBits :: [(Bits, Name)] -> [(Bits, [Name])]
groupByBits [] = [] -- So that we may assume xs is nonempty in the second line (so we can use head)
groupByBits xs = map (bisequence (fst . head, map snd)) $ groupBy ((==) `on` fst) xs

generateIntegerParsers :: Q Exp -> IntegerParserConfig -> Q [Dec]
generateIntegerParsers lexer cfg@IntegerParserConfig{..} = do
  (ubNames, concat -> ubDecs) <- unzip <$> mwhen includeUnbounded (lexerUnboundedParsers lexer cfg)
  (fwNames, fwBits, concat -> fwDecs) <- unzip3 <$> lexerFixedWidthIntParsers lexer cfg
  let fwBitsNames = groupByBits (zip fwBits fwNames)
  cDecs <- maybe mempty (mkCollatedParsers ubNames fwBitsNames) collatedParser
  return $ ubDecs <> fwDecs <> cDecs
 where
  mkCollatedParser :: [Name] -> String -> Q Type -> Q [Dec]
  mkCollatedParser [] _ _ = pure []
  mkCollatedParser (x : xs) nm tp = do
    f <- newName nm
    let body = foldl (\e y -> [|$e <|> $(varE y)|]) [|$(varE x)|] xs
    sequence
      [ pragInlD f Inline FunLike AllPhases
      , sigD f [t|Parsec $tp|]
      , funDsingleClause f body
      ]
  mkCollatedParsers :: [Name] -> [(Bits, [Name])] -> String -> Q [Dec]
  mkCollatedParsers xs bys nm =
    mkCollatedParser xs nm [t|Integer|]
      <> ( concat
            <$> forM
              bys
              ( \(b, nms) ->
                  let tp = fromJust (Map.lookup b widths)
                   in mkCollatedParser nms (bitsSuffix b nm) tp
              )
         )

bitsSuffix :: Bits -> String -> String
bitsSuffix B8 = (++ "8")
bitsSuffix B16 = (++ "16")
bitsSuffix B32 = (++ "32")
bitsSuffix B64 = (++ "64")

{- |

By default, the `prefix` field is the empty string.
-}
emptyIntegerParserConfig :: IntegerParserConfig
emptyIntegerParserConfig =
  IntegerParserConfig
    { prefix = ""
    , widths = Map.empty
    , bases = IntLitBases Set.empty
    , includeUnbounded = False
    , signedOrUnsigned = Signed
    , collatedParser = Nothing
    }

emptySignedIntegerParserConfig :: IntegerParserConfig
emptySignedIntegerParserConfig = emptyIntegerParserConfig{signedOrUnsigned = Signed}

emptyUnsignedIntegerParserConfig :: IntegerParserConfig
emptyUnsignedIntegerParserConfig = emptyIntegerParserConfig{signedOrUnsigned = Unsigned}

lexerUnboundedParsers ::
  -- | Quoted Lexer
  Q Exp ->
  IntegerParserConfig ->
  -- | The name and definition of each unbounded parsers
  Q [(Name, [Dec])]
lexerUnboundedParsers lexer (IntegerParserConfig{signedOrUnsigned = s, prefix, bases}) = do
  let proj = if isSigned s then [|integer|] else [|natural|]
  let parsers = filterByBase bases integerParsers
  forM
    parsers
    ( \p -> do
        newTp <- getLexerCombinatorType p False
        mkLexerCombinatorDecWithProj lexer (prefix ++ nameBase p) p (pure newTp) proj
    )

lexerFixedWidthIntParsers ::
  -- | The quoted lexer
  Q Exp ->
  -- | config
  IntegerParserConfig ->
  -- | Name, bitwidth and def of each generated combinator.
  Q [(Name, Bits, [Dec])]
lexerFixedWidthIntParsers
  lexer
  (IntegerParserConfig{signedOrUnsigned = sign, prefix, bases, widths}) =
    let proj = if isSigned sign then [|integer|] else [|natural|]
     in forM
          parsersToMake
          ( \(old, bw, newTp) -> do
              (nm, decs) <-
                mkLexerCombinatorDecWithProj
                  lexer
                  (prefix ++ nameBase old)
                  old
                  [t|Parsec $newTp|]
                  proj
              return (nm, bw, decs)
          )
   where
    parsersToMake :: [(Name, Bits, Q Type)]
    parsersToMake =
      concatMap
        (\(b, tp) -> map (,b,tp) (parsersAtWidth b))
        (Map.toList widths)
    parsersAtWidth :: Bits -> [Name]
    parsersAtWidth b = filterByBase bases $ case b of
      B8 -> intParsers8Bit
      B16 -> intParsers16Bit
      B32 -> intParsers32Bit
      B64 -> intParsers64Bit
