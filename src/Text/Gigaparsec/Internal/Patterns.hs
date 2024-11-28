{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE TemplateHaskell, CPP #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use fewer imports" #-}
{-# OPTIONS_GHC -Wno-monomorphism-restriction #-}
{-# OPTIONS_GHC -Wno-missing-kind-signatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# HLINT ignore "Use newtype instead of data" #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-|
Module      : Text.Gigaparsec.Internal.Patterns
Description : Common Template Haskell Utils
License     : BSD-3-Clause
Maintainer  : Jamie Willis, Gigaparsec Maintainers
Stability   : experimental

Common utils for patterns generated using Template Haskell.

@since 0.2.2.0
-}
module Text.Gigaparsec.Internal.Patterns (module Text.Gigaparsec.Internal.Patterns) where

import Language.Haskell.TH (TyVarBndr (KindedTV, PlainTV), Type (..), Specificity, Q, Extension (KindSignatures), isExtEnabled)
import Language.Haskell.TH.Syntax (Name)
import Data.List (union)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Bifunctor (Bifunctor(bimap))
import Control.Monad (foldM)
import Data.Functor.Foldable (Recursive (project, cata), Base, Corecursive (embed), zygo)
import GHC.Generics (Generic)

-- When KindSignatures is off, the default (a :: *) that TH generates is broken!
#if __GLASGOW_HASKELL__ >= 900
sanitiseStarT :: TyVarBndr flag -> TyVarBndr flag
sanitiseStarT (KindedTV ty flag _) = PlainTV ty flag
sanitiseStarT ty = ty
#else
sanitiseStarT :: TyVarBndr -> TyVarBndr
sanitiseStarT (KindedTV ty _) = PlainTV ty
sanitiseStarT ty = ty
#endif

-- | Remove stars from binder annotations when we don't have `KindSignatures` enabled.
#if __GLASGOW_HASKELL__ >= 900
sanitiseBndrStars :: [TyVarBndr flag] -> Q [TyVarBndr flag]
sanitiseBndrStars bndrs = do
  kindSigs <- isExtEnabled KindSignatures
  return (if kindSigs then bndrs else map sanitiseStarT bndrs)
#else
sanitiseBndrStars :: [TyVarBndr] -> Q [TyVarBndr]
sanitiseBndrStars bndrs = do
  kindSigs <- isExtEnabled KindSignatures
  return (if kindSigs then bndrs else map sanitiseStarT bndrs)
#endif


-- use this defn so that TypeF doesn't need to have two recursion params
type TyVarBndrF flag k = Either (Name, flag) (Name, flag, k)

{-# COMPLETE PlainTVF, KindedTVF #-}

pattern PlainTVF :: Name -> flag -> TyVarBndrF flag k
pattern PlainTVF n f = Left (n, f)

pattern KindedTVF :: Name -> flag -> k -> TyVarBndrF flag k
pattern KindedTVF n f knd = Right (n, f, knd)

pattern VarTF :: Name -> TypeF k
pattern VarTF nm = AtomicF (VarT nm)

type KindF k = TypeF k
data TypeF k = 
    ForallTF [TyVarBndrF Specificity k] [k] k
  | ForallVisTF [TyVarBndrF () k] k
  | AppTF k k
  | AppKindTF k k
  | SigTF k k
  | InfixTF k Name k
  | UInfixTF k Name k
  | PromotedInfixTF k Name k
  | PromotedUInfixTF k Name k
  | ImplicitParamTF String k
  | AtomicF Type
  | ParensTF k
  deriving stock (Functor, Foldable, Traversable, Generic)

-- data Fix f = In {inOp :: f (Fix f)}

type instance Base Type = TypeF

projectBnd :: TyVarBndr flag -> TyVarBndrF flag Type
projectBnd (PlainTV n f) = PlainTVF n f
projectBnd (KindedTV n f k) = KindedTVF n f k

embedBnd :: TyVarBndrF flag Type -> TyVarBndr flag
embedBnd (PlainTVF n f) = PlainTV n f
embedBnd (KindedTVF n f k) = KindedTV n f k

instance Recursive Type where
  project :: Type -> Base Type Type
  project = go
    where
    go :: Type -> Base Type Type
    go t = case t of
      ForallT bnds ctx a -> 
        ForallTF (handleBnds bnds) ctx a
      ForallVisT bnds a ->
        ForallVisTF (handleBnds bnds) a
      AppT a b -> AppTF a b
      AppKindT a k -> AppKindTF a k
      SigT a k -> SigTF a k
      InfixT a n b -> InfixTF a n b
      UInfixT a n b -> UInfixTF a n b
      PromotedInfixT a n b -> PromotedInfixTF a n b
      PromotedUInfixT a n b -> PromotedUInfixTF a n b
      ImplicitParamT x a -> ImplicitParamTF x a
      ParensT k -> ParensTF k
      a -> AtomicF a
    
    handleBnds :: [TyVarBndr flag] -> [TyVarBndrF flag Type]
    handleBnds = map (\case
        PlainTV n f ->  PlainTVF n f
        KindedTV n f k -> KindedTVF n f k
      )

instance Corecursive Type where
  embed :: Base Type Type -> Type
  embed t = case t of
    ForallTF bnds ctx a -> 
      ForallT (handleBnds bnds) ctx a
    ForallVisTF bnds a ->
      ForallVisT (handleBnds bnds) a
    AppTF a b -> AppT a b
    AppKindTF a k -> AppKindT a k
    SigTF a k -> SigT a k
    InfixTF a n b -> InfixT a n b
    UInfixTF a n b -> UInfixT a n b
    PromotedInfixTF a n b -> PromotedInfixT a n b
    PromotedUInfixTF a n b -> PromotedUInfixT a n b
    ImplicitParamTF x a -> ImplicitParamT x a
    ParensTF k -> ParensT k
    AtomicF a -> a

    where
    handleBnds :: [TyVarBndrF flag Type] -> [TyVarBndr flag]
    handleBnds = map (\case
        PlainTVF n f ->  PlainTV n f
        KindedTVF n f k -> KindedTV n f k
      )
-- class HasBaseFunctor a f where
--   toBaseFunctor :: a -> Fix f


-- instance HasBaseFunctor Type TypeF where
--   toBaseFunctor :: Type -> Fix TypeF
--   toBaseFunctor = In . go
--     where
--       go :: Type -> TypeF (Fix TypeF)
--       go t = case t of
--         ForallT bnds ctx a -> 
--           ForallTF (handleBnds bnds) (map go ctx) (toBaseFunctor a)
--         ForallVisT bnds a ->
--           ForallVisTF (handleBnds bnds) (toBaseFunctor a)
--         AppT a b -> AppTF (toBaseFunctor a) (toBaseFunctor b)
--         AppKindT a k -> AppKindTF (toBaseFunctor a) (go k)
--         SigT a k -> SigTF (toBaseFunctor a) (go k)
--         InfixT a n b -> InfixTF (toBaseFunctor a) n (toBaseFunctor b)
--         UInfixT a n b -> UInfixTF (toBaseFunctor a) n (toBaseFunctor b)
--         PromotedInfixT a n b -> PromotedInfixTF (toBaseFunctor a) n (toBaseFunctor b)
--         PromotedUInfixT a n b -> PromotedUInfixTF (toBaseFunctor a) n (toBaseFunctor b)
--         ImplicitParamT x a -> ImplicitParamTF x (toBaseFunctor a)
--         ParensT k -> ParensTF (toBaseFunctor k)
--         a -> AtomicF a
      
--       handleBnds :: [TyVarBndr flag] -> [TyVarBndrF flag (Fix TypeF)]
--       handleBnds = map (\case
--           PlainTV n f ->  PlainTVF n f
--           KindedTV n f k -> KindedTVF n f (go k)
        -- )

-- cata :: forall a . (TypeF a -> a) -> Type -> a
-- cata alg a = help (toBaseFunctor a)
--   where
--     help :: Fix TypeF -> a
--     help = alg . fmap help . inOp

-- cata' :: forall a . (TypeF a -> a) -> (TypeF) -> a
-- cata' = 

-- cataM :: forall m a . Monad m => (TypeF a -> m a) -> Type -> m a
-- cataM alg a = help (toBaseFunctor a)
--   where
--     help :: Fix TypeF -> m a
--     help (In t) = 
--       let foo = fmap help t 
--           bar = alg foo
--           baz = help t
--       in _

-- baseToType :: Fix TypeF -> Type
-- baseToType = _

-- use patterns to make backward compat?
-- also if I only pattern match on the F constructors, I can use a smart constructor for the rest


mkInfixT :: Type -> Name -> Type -> Type
mkUInfixT :: Type -> Name -> Type -> Type
mkParensT :: Type -> Type
#if MIN_VERSION_template_haskell(2,11,0)
mkParensT = ParensT
mkUInfixT = UInfixT
mkInfixT = InfixT
#elif
mkUInfixT = undefined
mkParensT = undefined
mkInfixT = undefined
#endif

mkAppKindT :: Type -> Type -> Type
mkImplicitParamT :: String -> Type -> Type
#if MIN_VERSION_template_haskell(2,15,0)
mkAppKindT = AppKindT
mkImplicitParamT = ImplicitParamT
#elif
mkAppKindT = undefined
mkImplicitParamT = undefined
#endif

mkForallVisT :: [TyVarBndr ()] -> Type -> Type
#if MIN_VERSION_template_haskell(2,16,0)
mkForallVisT bnds tp = ForallVisT bnds tp
#elif
mkForallVisT bnds tp = undefined
#endif

mkPromotedInfixT :: Type -> Name -> Type -> Type
mkPromotedUInfixT :: Type -> Name -> Type -> Type
#if MIN_VERSION_template_haskell(2,19,0)
mkPromotedInfixT = PromotedInfixT
mkPromotedUInfixT = PromotedUInfixT
#elif
mkPromotedInfixT = undefined
mkPromotedUInfixT = undefined
#endif

sanitiseTypeStars :: Type -> Q Type
sanitiseTypeStars = cata go
  where
    go :: TypeF (Q Type) -> Q Type
    go (ForallTF bnds ctx tp) =
      ForallT <$> mapM helpBnd bnds <*> sequence ctx <*> tp
    go (ForallVisTF bnds tp) = mkForallVisT <$> mapM helpBnd bnds <*> tp
    go e = embed <$> sequence e

    helpBnd :: TyVarBndrF flag (Q Type) -> Q (TyVarBndr flag)
    helpBnd (PlainTVF n f) = return $ PlainTV n f
    helpBnd (KindedTVF n f ~_) = return $ PlainTV n f

-- sanitiseTypeStars :: Type -> Q Type
-- sanitiseTypeStars (ForallT bnds ctx tp) = 
--   ForallT <$> sanitiseBndrStars bnds <*> return ctx <*> sanitiseTypeStars tp
-- sanitiseTypeStars (AppT a b) = 
--   AppT <$> sanitiseTypeStars a <*> sanitiseTypeStars b
-- sanitiseTypeStars (SigT a _) = 
--   sanitiseTypeStars a
-- #if MIN_VERSION_template_haskell(2,11,0)
-- sanitiseTypeStars (InfixT a n b) = 
--   InfixT <$> sanitiseTypeStars a <*> return n <*> sanitiseTypeStars b
-- sanitiseTypeStars (UInfixT a n b) =
--   UInfixT <$> sanitiseTypeStars a <*> return n <*> sanitiseTypeStars b
-- sanitiseTypeStars (ParensT a) = ParensT <$> sanitiseTypeStars a
-- #endif
-- #if MIN_VERSION_template_haskell(2,15,0)
-- sanitiseTypeStars (AppKindT a k) = AppKindT <$> sanitiseTypeStars a <*> sanitiseTypeStars k
-- sanitiseTypeStars (ImplicitParamT x a) = ImplicitParamT x <$> sanitiseTypeStars a
-- #endif
-- #if MIN_VERSION_template_haskell(2,16,0)
-- sanitiseTypeStars (ForallVisT bnds tp) =
--   ForallVisT <$> sanitiseBndrStars bnds <*> sanitiseTypeStars tp
-- #endif
-- #if MIN_VERSION_template_haskell(2,19,0)
-- sanitiseTypeStars (PromotedInfixT a n b) = 
--   PromotedInfixT <$> sanitiseTypeStars a <*> return n <*> sanitiseTypeStars b
-- sanitiseTypeStars (PromotedUInfixT a n b) = 
--   PromotedUInfixT <$> sanitiseTypeStars a <*> return n <*> sanitiseTypeStars b
-- #endif
-- sanitiseTypeStars a = return a

-- Left is the name bound by this scope, right is names that appear free (e.g. in kind annotations)
-- bndrFreeAndBoundNames :: TyVarBndrF flag k -> (Name, k)
-- bndrFreeAndBoundNames (PlainTV x _) = (x, Set.empty)
-- bndrFreeAndBoundNames (KindedTV x _ k) = (x, typeFreeVars k)

unTyVarBndrF :: TyVarBndrF flag k -> (Name, flag, Maybe k)
unTyVarBndrF (PlainTVF x f) = (x, f, Nothing)
unTyVarBndrF (KindedTVF x f k) = (x, f, Just k)

reTyVarBndr :: Name -> flag -> Maybe Type -> TyVarBndr flag
reTyVarBndr n f mt = case mt of
  Nothing -> PlainTV n f
  Just t -> KindedTV n f t

getBndrFName :: TyVarBndrF flag k -> Name
getBndrFName = (\(a,_,_) -> a) . unTyVarBndrF 
-- (PlainTVF x _) = x
-- getBndrFName (KindedTVF x _ _) = x

removeUnusedTVars :: Type -> Type
removeUnusedTVars = zygo typeFreeVarsAlg go
  where
    go :: TypeF (Set Name, Type) -> Type
    go (ForallTF bnds ctx (tpNames, tp) ) = 
      let (ctxNames, ctx') = unzip ctx 
          -- All names that *do* occur in the rest of the type/constraints
          allFreeNames = Set.unions (tpNames: ctxNames)
          (bnds', _) = foldr discardUnusedTVars ([], allFreeNames) bnds
      in  ForallT bnds' ctx' tp
    go (ForallVisTF bnds (tpNames, tp)) = 
      let (bnds', _) = foldr discardUnusedTVars ([], tpNames) bnds
      in  ForallVisT bnds' tp
    go e = embed (snd <$> e)
      -- embed <$> sequence _
    --  sequence e

    discardUnusedTVars :: TyVarBndrF s (Set Name, Type)
        -> ([TyVarBndr s], Set Name) 
        -> ([TyVarBndr s], Set Name)
    discardUnusedTVars bnd (bnds, names) = 
      let (n, f, mk) = unTyVarBndrF bnd
      in  if n `Set.member` names
            -- We keep n, and add any free vars in its kind (if it has one)
            then (reTyVarBndr n f (snd <$> mk) : bnds, 
              Set.union (maybe Set.empty fst mk) names)
            -- We discard n as it does not appear in subterms
            else (bnds, names)

    

typeFreeVarsAlg :: TypeF (Set Name) -> Set Name
typeFreeVarsAlg = go
  where
  go :: TypeF (Set Name) -> Set Name
  go (VarTF x) = Set.singleton x
  go (ForallTF bnds ctx tp) = handleBnds bnds (Set.unions $ (tp: ctx))
  go (ForallVisTF bnds tp) = handleBnds bnds tp
  go e = foldr Set.union Set.empty e

  handleBnds :: [TyVarBndrF flag (Set Name)] -> Set Name -> Set Name
  handleBnds bnds ns = 
    let (as, ks) = 
          bimap Set.fromList Set.unions $ unzip (map bndrFreeAndBoundNames bnds)
    in  Set.difference (Set.union ks ns) as
  
  bndrFreeAndBoundNames :: TyVarBndrF flag (Set Name) -> (Name, Set Name)
  bndrFreeAndBoundNames (PlainTVF x _) = (x, Set.empty)
  bndrFreeAndBoundNames (KindedTVF x _ k) = (x, k)


typeFreeVars :: Type -> Set Name
typeFreeVars = cata typeFreeVarsAlg

--   handleBnds bnds ns = 
--     let (as, ks) = bimap Set.fromList Set.unions $ unzip (map bndrFreeAndBoundNames bnds)
--     in  Set.difference (Set.union ks ns) as
--   go :: Type -> Set Name
--   go (ForallT bnds ctx tp) = handleBnds bnds (Set.unions $ map go (tp: ctx))
--   go (AppT a b) = Set.union (go a) (go b)
--   go (SigT a k) = Set.union (go a) (go k)
--   go (VarT x) = Set.singleton x
-- #if MIN_VERSION_template_haskell(2,11,0)
--   go (InfixT a _ b) = Set.union (go a) (go b)
--   go (UInfixT a _ b) = Set.union (go a) (go b)
--   go (ParensT a) = go a
-- #endif
-- #if MIN_VERSION_template_haskell(2,15,0)
--   go (AppKindT a k) = Set.union (go a) (go k)
--   go (ImplicitParamT _ a) = go a
-- #endif
-- #if MIN_VERSION_template_haskell(2,16,0)
--   go (ForallVisT bnds a) = handleBnds bnds (go a)
-- #endif
-- #if MIN_VERSION_template_haskell(2,19,0)
--   go (PromotedInfixT a _ b) = Set.union (go a) (go b)
--   go (PromotedUInfixT a _ b) = Set.union (go a) (go b)
-- #endif
--   go _ = Set.empty

