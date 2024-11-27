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
  lexerCombinatorsWithNames,
  ) where

import Text.Gigaparsec (Parsec)
import Text.Gigaparsec.Token.Lexer (Lexer (space), lexeme, sym, Symbol, symbol, Lexeme (..), Space, Names, CanHoldSigned, CanHoldUnsigned, TextParsers (..))

import Text.Gigaparsec.Internal.Patterns (sanitiseBndrStars, sanitiseTypeStars)

import Data.String (IsString(fromString))
import Language.Haskell.TH.Syntax (Q, Dec (..), Exp (VarE), Name (Name), OccName (OccName), reifyType, Type (ForallT), Quasi (qRecover), reifyInstances, reify, Quote (newName), nameBase, Body (..), Code, unTypeCode, isInstance, runIO, mkName, Inline (Inline), Phases (AllPhases), getDoc, DocLoc (DeclDoc), addModFinalizer, putDoc)

import Language.Haskell.TH (Type(MulArrowT), Pat (VarP), sigD, pprint, RuleMatch (FunLike))

import Language.Haskell.TH (Type (..), funD, clause, normalB, varE, Ppr (ppr), pragInlD)
import Control.Arrow (Arrow(first))
import Control.Monad (when, guard, unless)
import Control.Applicative (Alternative)
import Data.Kind (Constraint)
import Debug.Trace (trace)
import Text.Gigaparsec.Internal.Token.Numeric (IntegerParsers)
import Text.Gigaparsec.Internal.Token.Text (TextParsers)
import Data.Maybe (fromMaybe)
import Text.Gigaparsec.Token.Lexer qualified as Lexer

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
lexerCombinatorWithName lexer old nm = mkCombinator
  where
    -- Figures out how to construct the combinator;
    -- Calculates the domain type, and the return type of the new combinator.
    -- Calculates the definition of the combinator using either a typeclass (if possible), or deferring to 
    -- the specialised definitions.
    mkCombinator :: Q [Dec]
    mkCombinator = do
      tp <- reifyType old
      (prefix, dom, _, cod) <-
        fail (notFunctionTypeMsg old tp) `qRecover` fnTpDomain tp
      let newTp = prefix cod
      b <- isInstance ''LexerField [dom]
      if b 
        then mkDecNonSpecialised newTp
        else specialisedCombinators dom newTp

    -- Generate lexer combinators for TextParsers, as these are not unique per type,
    -- we need to manually derive these (can't rely on the LexerField class).
    specialisedCombinators :: Type -> Type -> Q [Dec]
    specialisedCombinators dom newTp
      -- Could wrap these in a `newtype SpecialisedField (a -> b) -> (Lexer -> b)`
      -- but seems like over-engineering
      --  | old == 'Lexer.stringLiteral = go [|| (. stringLiteral . lexeme) ||]
      --  | old == 'Lexer.rawStringLiteral = go [|| (. rawStringLiteral . lexeme) ||]
      --  | old == 'Lexer.multiStringLiteral = go [|| (. multiStringLiteral . lexeme) ||]
      --  | old == 'Lexer.rawMultiStringLiteral = go [|| (. rawMultiStringLiteral . lexeme) ||]
      | old == 'Lexer.ascii = failStringParser old
      | old == 'Lexer.unicode = failStringParser old
      | old == 'Lexer.latin1 = failStringParser old
      | otherwise = fail (notLexerFieldMsg old dom)
      where
        go :: Code Q (LexerProj a b) -> Q [Dec]
        go = mkDecSpecialised newTp 

    -- Message to give to the user when they give a TextParser field, as there is no way to disambiguate
    -- exactly *which* TextParser they want.
    -- And there is no point in implementing a way for the user to ask for this;
    -- at that point, it would be no more work on the user's end than were they to write a manual definition.
    failStringParser :: Name -> Q a
    failStringParser nm = fail $ concat [
        "Cannot derive a lexer combinator for `", pprint nm, 
        "`, as there are many possible ", pprint ''TextParsers, " to define it in terms of, including:",
        pprint 'stringLiteral, ", ",
        pprint 'rawStringLiteral, ", ",
        pprint 'multiStringLiteral, ", and ",
        pprint 'rawMultiStringLiteral, ".",
        "\n You will need to manually define this combinator, as you are then able to pick which TextParser it should use."
      ]

    -- When the `LexerField` class applies to the desired combinator,
    -- we can simply use the `project` function from that class.
    mkDecNonSpecialised
      :: Type -- The return type of the combinator to be formed
      -> Q [Dec]
    mkDecNonSpecialised tp = mkDecWith tp [| project |]
    
    -- When using a specialised field (e.g. a TextParser), then the (quoted) projection must be given.
    -- Prefer this quoted code to be *typed* so that it is easier to catch mistakes
    -- when defining them in `specialisedCombinators`.
    mkDecSpecialised
      :: Type -- The return type of the combinator to be formed
      -> Code Q (LexerProj a b) -- the quoted projection function
      -> Q [Dec]
    mkDecSpecialised tp field = 
      mkDecWith tp (unTypeCode field)

    -- This actually makes the new function definition, using the supplied projection function and new name.
    -- This declaration also provides a function signature and an INLINE pragma.
    mkDecWith
      :: Type -- The return type of the combinator to be formed
      -> Q Exp -- The projection function
      -> Q [Dec]
    mkDecWith tp proj = do
      newX <- newName nm
      oldDocs <- getDoc (DeclDoc old)
      let newDocs = fromMaybe "" oldDocs
      addModFinalizer $ putDoc (DeclDoc newX) newDocs
      sequence
        [ pragInlD newX Inline FunLike AllPhases
        , sigD newX (pure tp)
        , funD newX [clause [] (normalB [| $proj $(varE old) $lexer |]) []]
        ]

    -- If the quoted name is not a recognised lexer field, then we should tell the user as much.
    -- The error may be due to being able to disambiguate the field, rather than the field not existing.
    notLexerFieldMsg :: Name -> Type -> String
    notLexerFieldMsg x tp = concat [
        "Cannot produce a lexer combinator for function: ", pprint x, ".",
        "\n This is because the type: `", pprint tp, "` cannot be used to give a precise combinator, either because it does not refer to ",
        "any fields of a `Lexer`, or because it ambiguously refers to many fields of a `Lexer`.",
        "\n Some fields of the `Lexer` share the same type, so there are multiple possible candidate combinators for a particular field.",
        " For example: ",
        "\n   - `decimal`, `hexadecimal`,... all have type `IntegerParsers canHold -> Parsec Integer`.",
        "\n   - `ascii`, `unicode`, ... all have type `TextParsers t -> Parsec t`."
      ]

    -- If the quoted name is not at least a function type, then there's no real way to define the combinator :p
    notFunctionTypeMsg :: Name -> Type -> String
    notFunctionTypeMsg x tp = concat ["Constant `", show x,"` does not have a function type: ", show tp]


-- lexerUnsignedParsers 
--   :: Q Exp -- Quoted Lexer
--   -> String -- prefix for unsigned parsers
--   -> Q [Dec]
-- lexerUnsignedParsers = 

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


type LexerProj a b = (a -> b) -> (Lexer -> b)


---------------------------------------------------------------------------------------------------
-- Space

instance LexerField Space where
  {-# INLINE project #-}
  project :: (Space -> b) -> (Lexer -> b)
  project f = f . space
