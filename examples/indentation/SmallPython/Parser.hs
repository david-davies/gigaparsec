{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TupleSections, CPP #-}
{-# OPTIONS_GHC -Wno-missing-kind-signatures #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}


{-|
This module defines the parser for (small)python.
-}
module SmallPython.Parser where
import Prelude hiding (fail)

import Text.Gigaparsec hiding (some)
import Text.Gigaparsec.Combinator.NonEmpty


import SmallPython.Lexer
import SmallPython.AST
import Text.Gigaparsec.Position (pos)
import Text.Gigaparsec.Combinator (sepBy)
import Text.Gigaparsec.Char (endOfLine, newline)
import Text.Gigaparsec.Expr.Chain (chainr1)
import Text.Gigaparsec.Expr.Chain (chainr)
import Text.Gigaparsec.Expr.Infix (infixr1)
import Text.Gigaparsec.Expr qualified as Expr
import Text.Gigaparsec.Expr hiding (Atom)
import Text.Gigaparsec.Internal qualified as Internal



import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NonEmpty
import Control.Monad.Reader (ReaderT, Reader, MonadReader (local), MonadTrans (lift))
import Text.Gigaparsec.State (Ref)
import Data.IORef (IORef)
import Text.Gigaparsec.Errors.Combinator (fail)
import Text.Gigaparsec.Debug qualified as Debug
import Text.Gigaparsec.Combinator (sepEndBy, optional, whileS)
import SmallPython.AST.ToPython (ToPython(..))
import Text.Gigaparsec.Position (col)
import Control.Monad (unless, when)
import qualified Data.List.NonEmpty as NE
import Text.Gigaparsec.State (make)
import Text.Gigaparsec.State
import Text.Gigaparsec.Combinator (option)
import Data.Maybe (isJust)
import Text.Gigaparsec.Errors.Combinator ((<?>))

-- #define __SMALLPYTHON_DEBUG__
#define __GIGAPARSEC_DEBUG_INDENT__

{-# INLINE debug #-}
#ifdef __SMALLPYTHON_DEBUG__
debug :: forall a. String -> Parsec a -> Parsec a
debug = Debug.debug
#else
debug _ p = p
#endif

{-# INLINE debugIndent #-}
debugIndent :: forall a. String -> Parsec a -> Parsec a
#ifdef __GIGAPARSEC_DEBUG_INDENT__
debugIndent = Debug.debug
#else
debugIndent _ p = p
#endif

---------------------------------------------------------------------------------------------------
-- Atoms

number :: Parsec Atom
number = AtomNumber . AtomInt <$> integer

variable :: Parsec Atom
variable = AtomVar <$> ident

atom :: Parsec Expr
atom = mkExprAtom (
      variable
  <|> number)


---------------------------------------------------------------------------------------------------
-- Expressions

paren :: Parsec a -> Parsec a
paren p = "(" *> p <* ")"

parenChangeWs :: Parsec a -> Parsec a
parenChangeWs p = paren (alter isParenWhiteSpace (whiteSpace *> p))

args :: Parsec [Expr]
args = debug "args" $ parenChangeWs (sepBy (debug "arg" expr) ",")

functionCall :: Parsec (Expr -> Expr)
functionCall = debug "fcall" $ do
  info <- parseInfo
  us <- args
  return (\t -> ExprFunctionCall info t us )


expr :: Parsec Expr
expr = do
  info <- parseInfo
  t <- debug "exprtable" exprTable
  (debug "exprnotflw" (notFollowedBy "(") *> return t)
    <|> (debug "exprfcall" $ ExprFunctionCall info t <$> args)
  where
    exprBinApp 
      :: BinOpSymbol 
      -> Parsec ()
      -> Parsec (Expr -> Expr -> Expr)
    exprBinApp op symbol = debug ("exprbin") $ mkExprBin <*> (mkBinOp op <* symbol)

    exprTable = precedence $
        Expr.Atom (debug "eatom" atom <|> debug "eparen" (parenChangeWs expr))
      >+  sops Postfix [
            functionCall
          ]
      >+  sops InfixR [ 
            exprBinApp BinExponent "**"
          ]
      >+  sops InfixL [ 
            exprBinApp BinMult "*"
          , exprBinApp BinDiv "/"
          , exprBinApp BinFloorDiv "//" 
          ]
      >+  sops InfixL [
            exprBinApp BinPlus "+",
            exprBinApp BinMinus "-"
          ]

params :: Parsec Params
params = parenChangeWs (sepBy param ",")
  where
    param =
      (,) <$> ident 
          <*> (Just <$> ("=" *> expr) <|> return Nothing)

exprLHS :: Parsec ExprLHS
exprLHS = LHSIdent <$> ident

assignOp :: Parsec AssignType
assignOp = 
      ("="  $> AssignSimple)
  <|> ("+=" $> AssignPlus)


-- stats :: Parsec Stats
-- stats = 
--     -- chainr 
--     --   NonEmpty.singleton 
--     --   (stat)
--     --   (endOfLine $> NonEmpty.cons)

-- stats1 :: Parsec Stats1
-- stats1 = NonEmpty.fromList <$> 
  -- myIndentMany whiteSpace stat
  --   -- infixr1 
  --     NonEmpty.singleton 
  --     (stat currIndent)
  --     (endOfLine $> NonEmpty.cons)

functionDef :: Parsec Stat
functionDef = do
  lvl <- col
  mkFunctionDef ("def" *> ident) params 
        (":" *> endOfLine *> 
          (myIndentSome2 (Just lvl) whiteSpace stat)
        )

-- It seems better to just parse the lhs as an expression,
-- then have a fallible cast into a lhs.
-- lhs :: Parsec ExprLHS
-- lhs = exprToLHS <$> expr
--   where
--     exprToLHS

-- lhsOrExpr :: Parsec (Either ExprLHS Expr)
-- lhsorExpr = _

statExp :: Parsec Stat
statExp = mkStatExp (expr <* notFollowedBy assignOp)

exprToLHS :: Expr -> Parsec ExprLHS
exprToLHS t = case t of
  ExprAtom _ (AtomVar x) -> pure $ LHSIdent x
  _ -> fail $ ["The expression `", toPythonString t, "` is not a valid left-hand-side for assignment."]

{-| LHS of assignments and expressions have some common syntax.

Rather than do an expensive try of one or the other,
just parse a LHS as if it were an expression, then check if there is an assignment op.

* if there is, attempt to cast the parsed expression to a lhs (possibly failing w/ a message).
* if there is not, then we have parsed an expression statement

-}
statAssignOrExp :: Parsec Stat
statAssignOrExp = do
  t <- expr
  (assignOp >>= \op -> mkStatAssign (exprToLHS t) (pure op) expr)
    <|> mkStatExp (pure t)


-- statAssignment :: Expr

stat :: Parsec Stat
stat = 
      debug "fdef" (functionDef)
  <|> debug "statAsgnOrExp" (statAssignOrExp)
  <|> debug "return" (mkReturn ("return" *> expr))

program :: Parsec Program
program = fully $ many nextLine *> (Program <$> sepEndBy (nonIndented whiteSpace stat) (many nextLine))


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

type IndentLevel = Word

nonIndented :: Parsec () -> Parsec b -> Parsec b
nonIndented ws p = do
  ws
  lvl <- debug "CHECKING LEVEL" col
  debug (concat @[] ["LVL is ", show lvl, "!"]) (unless (lvl == 1) $ fail (NE.fromList ["bruh"]))
  p


indentLevel :: Parsec IndentLevel 
indentLevel = col

incorrectIndent :: Ordering -> IndentLevel -> IndentLevel -> Parsec a
incorrectIndent ord refLvl actLvl = fail ("Bad indent you no indent right" :| [])

whenM :: Monad m => m Bool -> m () -> m ()
whenM c f = c >>= \b -> when b f

indentManyAfter :: Parsec a -> Parsec () -> Parsec b -> Parsec (a, [b])
indentManyAfter p ws q = do
  lvl <- indentLevel
  (,) <$> p <*> myIndentMany (Just lvl) ws q

{-|
Use this infix:

@
 p `thenIndent` q
@

-}
thenIndent :: Parsec a -> Parsec () -> Parsec b -> Parsec (a, [b])
thenIndent = indentManyAfter

myIndentMany
  :: MIndentLevel
  -> Parsec () -- whitespace consumer, must consume newlines
  -> Parsec b  -- the indented items to parse
  -> Parsec [b]
myIndentMany mlvl ws p = make (fromOldIndent mlvl) $ \ref -> do
  optional endOfLine *> ws
  many (indentedItem ref)
  where
    indentedItem ref = do
      atomic (wsNL *> checkIndentLvl ref)
      (debug "indented item" p)

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
  :: MIndentLevel
  -> Parsec () -- whitespace consumer, must consume newlines
  -> Parsec b  -- the indented items to parse
  -> Parsec (NonEmpty b)
myIndentSome mlvl ws p = make (fromOldIndent mlvl) $ \ref -> do
  ws
  some (indentedItem ref)
  where
    indentedItem ref = do
      atomic ((debug "indented newline" wsNL) *> checkIndentLvl ref)
      (debug "indented item" p)

    wsNL = (ws *> optional endOfLine *> ws)

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


-- indentBlock :: forall b . 



-- Doesn't do atomic, does consume last newline
myIndentSome2
  :: forall b . 
     MIndentLevel
  -> Parsec () -- whitespace consumer, does not need to consume newlines
  -> Parsec b  -- the indented items to parse
  -> Parsec (NonEmpty b)
myIndentSome2 mlvl ws p = 
  make (fromOldIndent mlvl) $ \indentRef -> do
    optional endOfLine *> ws
    some (indentedItem indentRef)
  where
    indentedItem :: Ref r₂ IndentConfig ->  Parsec b
    indentedItem indentRef = do
      checkIndentLvl indentRef
      p <* endOfInputOrLine

    endOfInputOrLine :: Parsec ()
    endOfInputOrLine = (eof <|> eols) <?> ["end of indent block"]

    -- At least one end of line
    eols :: Parsec ()
    eols = void $ many (endOfLine *> ws)

    -- It is essential that this does not consume input
    checkIndentLvl ref = do
      -- do we need to check `eof` here?
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








-- singleStat :: IndentParser Stat
-- singleStat = 
--       ((lift endOfLine) *> singleStat)
--   <|> (mkFunctionDef ("def" *> ident) params (":" *> endOfLine *> indentBlock stat))

-- indentBlock :: Parsec a -> Parsec a
-- indentBlock p = _

-- newtype Indentation = Indentation Word

-- incIndent :: Indentation -> Indentation
-- incIndent (Indentation n) = Indentation (n + 1)

-- type IndentParser = ReaderT Indentation Parsec

-- class IsParser p where

-- indentRef :: IORef Indentation
-- indentRef = _

-- indentAfter :: IndentParser a -> IndentParser b -> IndentParser (a, b)
-- indentAfter p q = do
--   x <- p
--   y <- local incIndent q
--   return (x, y)
-- -- indentAfter p = Internal.Parsec $ \st ok err -> _

-- -- indentBlock :: 

-- type IndentParser2 a = Reader Indentation (Parsec a)

-- singleStat2 :: IndentParser2 Stat
-- singleStat2 = 
--       (endOfLine *> singleStat2)
--   <|> (mkFunctionDef ("def" *> ident) params (":" *> endOfLine *> indentBlock2 stat))


-- indentAfter2 :: IndentParser2 a -> IndentParser2 b -> IndentParser2 (a, b) 
-- indentAfter2 p q = do
--   x <- p
--   y <- local incIndent q
--   return $ (,) <$> x <*> y

-- indentBlock2 :: IndentParser2 a -> IndentParser2 a
-- indentBlock2 = local incIndent
