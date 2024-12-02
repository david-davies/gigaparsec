{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-missing-kind-signatures #-}
{-# OPTIONS_GHC -Wno-missing-deriving-strategies #-}
{-# OPTIONS_GHC -Wno-missing-role-annotations #-}
{-# OPTIONS_GHC -Wno-missing-import-lists #-}
module Text.Gigaparsec.Token.Indentation where

import Prelude hiding (fail)
import Data.List.NonEmpty (NonEmpty((:|)))
import Text.Gigaparsec (Parsec, atomic, eof)
import Text.Gigaparsec.Errors.Combinator (fail)
import Text.Gigaparsec.Position (col)
import Text.Gigaparsec.Char (endOfLine, newline)
import Text.Gigaparsec.Combinator (option, guardS, whenS, ifS)
import Data.Maybe (isJust, fromMaybe)
import Text.Gigaparsec.State (make, set, get, Ref)
import Control.Applicative (many, empty)
import Control.Monad (unless)
import Text.Gigaparsec.Combinator.NonEmpty (some)
import Text.Gigaparsec.Debug
import Data.List.NonEmpty qualified as NE

type IndentLevel = Word

data IndentOpt a b = 
    {-|
    Parse no indented tokens, just return the value.
    -}
    IndentNone a
  | {-|
    Parse zero or more indented tokens which start at the given indentation level, collecting their results.

    @`IndentMany` mlvl f p@ uses the given indentation level @mlvl@;
    if @mlvl@ `Nothing`, then uses the indentation level of the first token.
    Then, repeatedly parses @p@ at the indentation level, once per newline.
    Then, applies @f@ to the results @x₁@, ..., @xₙ@ from each parse of @p@ (where @n@ ≥ 0),
    i.e. @f [x₁, ..., xₙ]@
    -} 
    IndentMany 
      (Maybe IndentLevel) -- ^ The indentation at which the first token should start.
      ([b] -> Parsec a)   -- ^ What to do with the parsed lines.
      (Parsec b)          -- ^ How to parse each indented line.
  | {-|
    Parse one or more indented tokens which start at the given indentation level, collecting their results.

    @`IndentSome` mlvl f p@ uses the given indentation level @mlvl@;
    if @mlvl@ `Nothing`, then uses the indentation level of the first token.
    Then, repeatedly parses @p@ at the indentation level, once per newline.
    Then, applies @f@ to the results @x₁@, ..., @xₙ@ from each parse of @p@ (where @n@ ≥ 1),
    i.e. @f [x₁, ..., xₙ]@
    -}  
    IndentSome 
      (Maybe IndentLevel)      -- ^ The indentation at which the first token should start.
      (NonEmpty b -> Parsec a) -- ^ What to do with the parsed lines.
      (Parsec b)               -- ^ How to parse each indented line.

indentLevel :: Parsec IndentLevel 
indentLevel = col

incorrectIndent :: Ordering -> IndentLevel -> IndentLevel -> Parsec a
incorrectIndent ord refLvl actLvl = fail ("Bad indent you no indent right" :| [])

indentGuard 
  :: Parsec ()  -- ^ whitespace parser
  -> Ordering 
  -> IndentLevel       -- ^ reference indent level
  -> Parsec IndentLevel
indentGuard ws ord refLvl = do
  actLvl <- ws *> indentLevel
  if compare actLvl refLvl == ord
    then return actLvl
    else incorrectIndent ord refLvl actLvl

indentBlock 
  :: Parsec () -- ^ Whitespace parser
  -> Parsec (IndentOpt a b) -- ^ How to parse a reference token
  -> Parsec a -- ^ 
indentBlock ws p = do
  refLvl <- ws *> indentLevel
  refToken <- p
  case refToken of
    IndentNone x -> pure x
    IndentMany indentLvl ret item -> do
      mLvl <- option $ atomic (endOfLine *> indentGuard ws GT refLvl)
      done <- isJust <$> option eof
      case (mLvl, done) of
        (Just lvl, False) -> 
          ret =<< indentedItems ws refLvl (fromMaybe lvl indentLvl) item
        _ -> ws *> ret []
    IndentSome indentLvl ret parseSingleLine -> do
      pos <- endOfLine *> indentGuard ws GT refLvl
      let lvl = fromMaybe pos indentLvl
      x <- if
          | lvl <= refLvl -> incorrectIndent GT refLvl lvl
          | lvl == refLvl -> parseSingleLine
          | otherwise     -> incorrectIndent EQ lvl pos
      ret . (x :|) =<< indentedItems ws refLvl lvl parseSingleLine

indentedItems :: Parsec () -> IndentLevel -> IndentLevel -> Parsec a -> Parsec [a]
indentedItems ws refLvl itemLvl item =
  make False $ \ref -> do
    ws
    (many $ do
      guardS (do
          done <-  isJust <$> option eof 
          pos  <- indentLevel
          return $ (not done) && pos > refLvl
        )
      ifS 
        ((itemLvl ==) <$> indentLevel) 
        (item <* ws) 
        (set ref True *> empty)
      ) <* whenS (get ref) (incorrectIndent EQ refLvl itemLvl)
      
    -- lvl <- ws *> indentLevel

    -- done <- isJust <$> option eof 
    -- if done 
    --   then return []
    --   else


unlessM :: Monad m => m Bool -> m () -> m ()
unlessM f g = f >>= \b -> unless b g

data IndentType 
  = IndentTypeMany
  | IndentTypeSome

type MIndentLevel = Maybe Word

-- An indent level, and whether we should be gt or eq to it.
-- Maybe (Word, Ordering)
data IndentConfig =
    NewIndent
  | OldIndent  { unIndentConfig :: Word }
  | CurrIndent { unIndentConfig :: Word }
  
fromOldIndent :: MIndentLevel -> IndentConfig
fromOldIndent Nothing = NewIndent
fromOldIndent (Just x) = OldIndent x

toIndentLevel :: IndentConfig -> MIndentLevel
toIndentLevel NewIndent = Nothing
toIndentLevel (OldIndent x) = Just x
toIndentLevel (CurrIndent x) = Just x


nonIndented :: Parsec () -> Parsec b -> Parsec b
nonIndented ws p = do
  ws
  lvl <- debug "CHECKING LEVEL" col
  debug (concat ["LVL is ", show lvl, "!"]) (unless (lvl == 1) $ fail (NE.fromList ["bruh"]))
  p
  -- indentGuard ws EQ 1 *> p

myIndentMany
  :: Parsec () -- whitespace consumer, must consume newlines
  -> Parsec b  -- the indented items to parse
  -> Parsec [b]
myIndentMany ws p = make NewIndent $ \ref -> do
  ws
  many (indentedItem ref)
  where
    indentedItem ref = do
      checkIndentLvl ref
      p <* ws

    wsNL = (ws *> endOfLine *> ws)

    checkIndentLvl ref = do
      newIndentLvl <- indentLevel
      !mExpectedIndentLvl <- get ref
      case mExpectedIndentLvl of
        NewIndent 
          -> set ref (CurrIndent newIndentLvl)
        OldIndent  expectedIndentLvl 
          | expectedIndentLvl < newIndentLvl -> set ref (CurrIndent newIndentLvl)
        CurrIndent expectedIndentLvl 
          | expectedIndentLvl == newIndentLvl -> pure ()
        _ -> incorrectIndent2 mExpectedIndentLvl newIndentLvl

    incorrectIndent2 mExpected newIndentLvl = fail ("woops" :| [])

myIndentSome
  :: Parsec ()  -- ^ does not consume newlines
  -> MIndentLevel -- ^ old indent level
  -> (MIndentLevel -> Parsec a)   
  -- ^ how to parse a token at each indentation (i guess technically this may be more than one line)
  -- parameterised by the new indentation
  -> Parsec (NonEmpty a) -- ^
myIndentSome ws oldIndent line = make (fromOldIndent oldIndent) $ \ref -> do
  -- should we consume an initial newline?
  ws -- consume any initial whitespace
  -- consume newline and whitespace after a successful line
  -- if we consumed whitespace within indentedLine, then failing the indentation check
  -- would cause this `many` combinator to fail as we would have consumed input (the whitespace).
  some (indentedLine ref <* newline <* ws)

  where
    indentedLine ref = checkIndentLvl ref *> (line . toIndentLevel =<<  get ref)

    -- Compare the indent of the new item with the expected indentation
    -- If the latter is Nothing, then update it.
    checkIndentLvl ref = do
      newIndentLvl <- indentLevel
      !mExpectedIndentLvl <- get ref

      case mExpectedIndentLvl of
        NewIndent 
          -> set ref (CurrIndent newIndentLvl)

        OldIndent  expectedIndentLvl 
          | expectedIndentLvl < newIndentLvl -> set ref (CurrIndent newIndentLvl)

        CurrIndent expectedIndentLvl 
          | expectedIndentLvl == newIndentLvl -> pure ()

        _ -> incorrectIndent2 mExpectedIndentLvl newIndentLvl

    incorrectIndent2 mExpected newIndentLvl = fail ("woops" :| [])

