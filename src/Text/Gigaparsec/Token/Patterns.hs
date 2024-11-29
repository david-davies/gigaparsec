{-# LANGUAGE Safe #-}
{-# LANGUAGE TemplateHaskell, TypeOperators, CPP, UnicodeSyntax, ExistentialQuantification #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-unused-do-bind #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleInstances #-}

{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, TemplateHaskell, TypeFamilies #-}
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
  lexerUnsignedParsers,
  lexerUnsignedFixedWidthParsers,
  ) where

import Text.Gigaparsec (Parsec)
import safe Text.Gigaparsec.Internal.Token.Lexer
    ( Space,
      Lexeme(charLiteral, names, symbol, natural, sym, stringLiteral,
             rawStringLiteral, multiStringLiteral, rawMultiStringLiteral),
      Lexer(space, lexeme) )
import safe Text.Gigaparsec.Internal.Token.Names ( Names )
import safe Text.Gigaparsec.Internal.Token.Symbol ( Symbol )
import safe Text.Gigaparsec.Internal.Token.Text ( TextParsers )

import Text.Gigaparsec.Internal.TH.TypeUtils (sanitiseBndrStars, sanitiseTypeStars, removeUnusedTVars, getRecordFields)

import Data.String (IsString(fromString))
import Language.Haskell.TH.Syntax (Q, Dec (..), Exp (VarE), reifyType, Type (ForallT), Quasi (qRecover), Quote (newName), nameBase, isInstance, Inline (Inline), Phases (AllPhases), getDoc, DocLoc (DeclDoc), addModFinalizer, putDoc)

import Language.Haskell.TH (sigD, pprint, RuleMatch (FunLike))


import Language.Haskell.TH (Type (..), funD, clause, normalB, varE, pragInlD, reifyType)
import Control.Arrow (Arrow(first))
import Data.Kind (Constraint)
import Data.Maybe (fromMaybe)
import Text.Gigaparsec.Token.Lexer qualified as Lexer
import Text.Gigaparsec.Internal.TH.VersionAgnostic (Name, isExtEnabled, Extension (DataKinds))
import Language.Haskell.TH (reify, nameBase)
import Control.Monad (forM, mapM)
import Text.Gigaparsec.Internal.Token.BitBounds (Bits (..))

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
Generate the given lexer combinators from a lexer.

__Usage:__

> import Text.Gigaparsec.Token.Lexer qualified as Lexer
> import Text.Gigaparsec.Token.Lexer (Lexer)
> lexer :: Lexer
> $(lexerCombinators [| lexer |] ['Lexer.lexeme, 'Lexer.fully, 'Lexer.identifier, 'Lexer.stringLiteral])
> -- This will generate the following definitions:
> Lexer.Lexeme
    lexeme_a7oi
      = Text.Gigaparsec.Token.Patterns.project Lexer.lexeme lexer

-}
lexerCombinators
  :: Q Exp -- The lexer
  -> [Name] -- The combinators to generate
  -> Q [Dec]
lexerCombinators lexer ns = lexerCombinatorsWithNames lexer (zip ns (map nameBase ns))

{-|
Generate the given lexer combinators with custom names, from a lexer.
-}
lexerCombinatorsWithNames
  :: Q Exp -- The lexer
  -> [(Name, String)] -- The combinators to generate
  -> Q [Dec]
lexerCombinatorsWithNames lexer = fmap concat . traverse (uncurry (lexerCombinatorWithName lexer))

{-|
Create a single lexer combinator with a given name, defined in terms of the lexer.
-}
lexerCombinatorWithName
  :: Q Exp
  -> Name -- The name of the old combinator
  -> String -- the new name of the combinator
  -> Q [Dec]
lexerCombinatorWithName lexer old nm = do
  newTp <- getLexerCombinatorType old True
  mkLexerCombinatorDec lexer nm old newTp
  where

    -- This actually makes the new function definition with the new name.
    -- The type of `old` at this point is assumed to be in `LexerField`, so that we may define the function in terms of `project`.
    -- This declaration also provides a function signature and an INLINE pragma.
    mkDec
      :: Type -- The return type of the combinator to be formed
      -> Q [Dec]
    mkDec tp = do
      newX <- newName nm
      oldDocs <- getDoc (DeclDoc old)
      let newDocs = fromMaybe "" oldDocs
      addModFinalizer $ putDoc (DeclDoc newX) newDocs
      sequence
        [ pragInlD newX Inline FunLike AllPhases
        , sigD newX (pure tp)
        , funD newX [clause [] (normalB [| project $(varE old) $lexer |]) []]
        ]



-- | Constructs the combinator using the given type.
-- Calculates the definition of the combinator using a typeclass (if possible).
mkLexerCombinatorDec
  :: Q Exp  -- ^ The quoted Lexer
  -> String -- ^ The name of the combinator to generate
  -> Name   -- ^ The quoted name of the original combinator
  -> Type   -- ^ The return type of the new combinator
  -> Q [Dec]
mkLexerCombinatorDec lexer nm old tp = do
  newX <- newName nm
  oldDocs <- getDoc (DeclDoc old)
  let newDocs = fromMaybe "" oldDocs
  addModFinalizer $ putDoc (DeclDoc newX) newDocs
  sequence
    [ pragInlD newX Inline FunLike AllPhases
    , sigD newX (pure tp)
    , funD newX [clause [] (normalB [| project $(varE old) $lexer |]) []]
    ]

-- | Constructs the combinator using the given type.
-- Calculates the definition of the combinator using a typeclass (if possible).
mkLexerCombinatorDecWithProj
  :: Q Exp  -- ^ The quoted Lexer
  -> String -- ^ The name of the combinator to generate
  -> Name   -- ^ @old@, The quoted name of the original combinator
  -> Type   -- ^ The return type of the new combinator
  -> Q Exp  -- ^ projection to precompose the @old@ combinator with
  -> Bool   -- ^ add signature
  -> Q [Dec]
mkLexerCombinatorDecWithProj lexer nm old tp proj addSig = do
  newX <- newName nm
  oldDocs <- getDoc (DeclDoc old)
  let newDocs = fromMaybe "" oldDocs
  addModFinalizer $ putDoc (DeclDoc newX) newDocs
  sequence $
        pragInlD newX Inline FunLike AllPhases 
    :   [sigD newX (pure tp) | addSig]
    ++  [funD newX [clause [] (normalB [| project ($(varE old) . $proj) $lexer |]) []]]


-- | Figures out the type of the combinator minus the domain; this will be one of a 'Lexer' component, or any other subcomponents (e.g. 'Symbol' or 'Space').
-- Calculates the domain type, and the return type of the new combinator.
-- The boolean flag set to True means one should ensure the domain type gives a specific combinator,
-- and doesn't lead to an ambiguous return type.
getLexerCombinatorType :: Name -> Bool -> Q Type
getLexerCombinatorType old checkType = do
  tp <- reifyType old
  (prefix, dom, _, cod) <-
    fail (notFunctionTypeMsg old tp) `qRecover` fnTpDomain tp
  let newTp = prefix cod
  ~b <- isInstance ''LexerField [dom]
  if checkType && not b
    then catchErrors dom newTp
    else return $ prefix cod

  where
    -- If the quoted name is not at least a function type, then there's no real way to define the combinator :p
    notFunctionTypeMsg :: Name -> Type -> String
    notFunctionTypeMsg x tp = concat ["Constant `", nameBase x,"` does not have a function type: ", show tp]

        -- Preventative Errors: catch the cases someone tries to define one of the String or Integer parsers
    -- they should do these manually or with the bespoke generators!
    catchErrors :: Type -> Type -> Q a
    catchErrors dom newTp
      | old == 'Lexer.ascii = failStringParser old
      | old == 'Lexer.unicode = failStringParser old
      | old == 'Lexer.latin1 = failStringParser old
      | otherwise = fail (notLexerFieldMsg old dom)

    -- Message to give to the user when they give a TextParser field, as there is no way to disambiguate
    -- exactly *which* TextParser they want.
    -- And there is no point in implementing a way for the user to ask for this;
    -- at that point, it would be no more work on the user's end than were they to write a manual definition.
    failStringParser :: Name -> Q a
    failStringParser nm = fail $ concat [
        "Cannot derive a lexer combinator for `", nameBase nm,
        "`, as there are many possible ", pprint ''TextParsers, " to define it in terms of, including:",
        pprint 'stringLiteral, ", ",
        pprint 'rawStringLiteral, ", ",
        pprint 'multiStringLiteral, ", and ",
        pprint 'rawMultiStringLiteral, ".",
        "\n You will need to manually define this combinator, as you are then able to pick which TextParser it should use."
      ]

    -- If the quoted name is not a recognised lexer field, then we should tell the user as much.
    -- The error may be due to being able to disambiguate the field, rather than the field not existing.
    notLexerFieldMsg :: Name -> Type -> String
    notLexerFieldMsg x tp = concat [
        "Cannot produce a lexer combinator for function: ", nameBase x, ".",
        "\n This is because the type: `", pprint tp, "` cannot be used to give a precise combinator, either because it does not refer to ",
        "any fields of a `Lexer`, or because it ambiguously refers to many fields of a `Lexer`.",
        "\n Some fields of the `Lexer` share the same type, so there are multiple possible candidate combinators for a particular field.",
        " For example: ",
        "\n   - `decimal`, `hexadecimal`,... all have type `IntegerParsers canHold -> Parsec Integer`.",
        "\n   - `ascii`, `unicode`, ... all have type `TextParsers t -> Parsec t`."
      ]



integerParsers :: [Name]
integerParsers = [
    'Lexer.decimal
  , 'Lexer.hexadecimal
  , 'Lexer.octal
  , 'Lexer.binary
  ]

intParsers8Bit :: [Name]
intParsers8Bit = [
    'Lexer.decimal8
  , 'Lexer.octal8
  , 'Lexer.hexadecimal8
  , 'Lexer.binary8
  ]

intParsers16Bit :: [Name]
intParsers16Bit = [
    'Lexer.decimal16
  , 'Lexer.hexadecimal16
  , 'Lexer.octal16
  , 'Lexer.binary16
  ]

intParsers32Bit :: [Name]
intParsers32Bit = [
    'Lexer.decimal32
  , 'Lexer.hexadecimal32
  , 'Lexer.octal32
  , 'Lexer.binary32
  ]

intParsers64Bit :: [Name]
intParsers64Bit = [
    'Lexer.decimal64
  , 'Lexer.hexadecimal64
  , 'Lexer.octal64
  , 'Lexer.binary64
  ]

-- integerParsersFixedWidth :: [Name]
-- integerParsersFixedWidth = [
--     'Lexer.decimal8
--   , 'Lexer.octal8
--   , 'Lexer.hexadecimal8
--   , 'Lexer.binary8
--   , 'Lexer.decimal16
--   , 'Lexer.hexadecimal16
--   , 'Lexer.octal16
--   , 'Lexer.binary16
--   , 'Lexer.decimal32
--   , 'Lexer.hexadecimal32
--   , 'Lexer.octal32
--   , 'Lexer.binary32
--   , 'Lexer.decimal64
--   , 'Lexer.hexadecimal64
--   , 'Lexer.octal64
--   , 'Lexer.binary64
--   ]

lexerUnsignedParsers
  :: Q Exp -- Quoted Lexer
  -> String -- prefix for unsigned parsers
  -> Q [Dec]
lexerUnsignedParsers lexer prfx =
  concat <$> forM integerParsers (\p -> do
      newTp <- getLexerCombinatorType p False
      mkLexerCombinatorDecWithProj lexer (prfx ++ nameBase p) p newTp [|natural|] True
    )
  -- let x = 'Lexer.natural
  -- let old = 'Lexer.decimal
  -- tp <- reifyType old
  -- (prefix, dom, _, cod) <-
  --       fail "naw" `qRecover` fnTpDomain tp
  -- let newTp = prefix cod
  -- mkLexerCombinatorDec lexer (prfx ++ nameBase old) old newTp

{-| Supply which bitwidths desired, and what their return types should be.

-}
lexerUnsignedFixedWidthParsers :: Q Exp -> [Char] -> [(Bits, Q Type)] -> Q [Dec]
lexerUnsignedFixedWidthParsers lexer prfx bitAndTypes =
  concat <$> forM parsersToMake (\(old, newTp) -> do
      mkDec old newTp
    )
  where
    parsersToMake :: [(Name, Q Type)]
    parsersToMake = concatMap (\(b, tp) -> map (,tp) (parsersAtWidth b)) bitAndTypes
    parsersAtWidth :: Bits -> [Name]
    parsersAtWidth b = case b of
      B8 -> intParsers8Bit
      B16 -> intParsers16Bit
      B32 -> intParsers32Bit
      B64 -> intParsers64Bit

    mkDec :: Name -> Q Type -> Q [Dec]
    mkDec old tp = do
      newX <- newName (prfx ++ nameBase old)
      oldDocs <- getDoc (DeclDoc old)
      let newDocs = fromMaybe "" oldDocs
      addModFinalizer $ putDoc (DeclDoc newX) newDocs
      sequence $ [
        pragInlD newX Inline FunLike AllPhases 
        , sigD newX [t| Parsec $tp |]
        , funD newX [clause [] (normalB [| project ($(varE old) . natural) $lexer |]) []]
        ]

---------------------------------------------------------------------------------------------------
-- Util functions

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
  (a, (b,c,d)) <- fnTpDomain' =<< sanitiseTypeStars x
  return (removeUnusedTVars . a,b,c, d)
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

Avoid writing instances for:
- IntegerParsers
- TextParsers String

As this leads to ambiguous projections if users try to generate combinators for, e.g., 'Lexer.decimal.
There are two possible instances here, one for `integer`, the other for `natural`, and there is no way to disambiguate here.
By avoiding writing these instances, we can give the user a more informative error message should they try this.
-}
type LexerField :: * -> Constraint
class LexerField a where
  project :: (a -> b) -> (Lexer -> b)

type LexerProj :: * -> * -> *
type LexerProj a b = (a -> b) -> (Lexer -> b)


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
