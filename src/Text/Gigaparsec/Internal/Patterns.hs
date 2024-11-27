{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE TemplateHaskell, CPP #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use fewer imports" #-}
{-# OPTIONS_GHC -Wno-monomorphism-restriction #-}
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

sanitiseTypeStars :: Type -> Q Type
sanitiseTypeStars (ForallT bnds ctx tp) = 
  ForallT <$> sanitiseBndrStars bnds <*> return ctx <*> sanitiseTypeStars tp
sanitiseTypeStars (ForallVisT bnds tp) =
  ForallVisT <$> sanitiseBndrStars bnds <*> sanitiseTypeStars tp
sanitiseTypeStars (AppT a b) = 
  AppT <$> sanitiseTypeStars a <*> sanitiseTypeStars b
sanitiseTypeStars (AppKindT a k) = AppKindT <$> sanitiseTypeStars a <*> sanitiseTypeStars k
sanitiseTypeStars (SigT a _) = 
  sanitiseTypeStars a
sanitiseTypeStars (InfixT a n b) = 
  InfixT <$> sanitiseTypeStars a <*> return n <*> sanitiseTypeStars b
sanitiseTypeStars (UInfixT a n b) =
  UInfixT <$> sanitiseTypeStars a <*> return n <*> sanitiseTypeStars b
#if __GLASGOW_HASKELL__ >= 900
sanitiseTypeStars (PromotedInfixT a n b) = 
  PromotedInfixT <$> sanitiseTypeStars a <*> return n <*> sanitiseTypeStars b
sanitiseTypeStars (PromotedUInfixT a n b) = 
  PromotedUInfixT <$> sanitiseTypeStars a <*> return n <*> sanitiseTypeStars b
#endif
sanitiseTypeStars (ParensT a) = ParensT <$> sanitiseTypeStars a
sanitiseTypeStars (ImplicitParamT x a) = return WildCardT
sanitiseTypeStars a = return a

