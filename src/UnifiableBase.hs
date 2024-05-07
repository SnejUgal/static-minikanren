{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module UnifiableBase where

import GHC.Exts (IsList (..))
import GHC.Generics

import Control.Lens (Prism, Prism', prism)
import Control.Lens.TH (makePrisms)
import Core
import Data.Void (Void)
import DeriveLogic
import GenericUnifiable

deriveLogic ''Either
makePrisms ''LogicEither

data LogicList a
  = LogicNil
  | LogicCons (ValueOrVar a) (ValueOrVar [a])
  deriving (Generic)

_LogicNil :: Prism' (LogicList a) ()
_LogicNil = prism (const LogicNil) $ \case
  LogicNil -> Right ()
  LogicCons x xs -> Left (LogicCons x xs)

_LogicCons :: Prism (LogicList a) (LogicList b) (ValueOrVar a, ValueOrVar [a]) (ValueOrVar b, ValueOrVar [b])
_LogicCons = prism (uncurry LogicCons) $ \case
  LogicCons x xs -> Right (x, xs)
  LogicNil -> Left LogicNil

deriving instance (Show (Term a)) => Show (LogicList a)

instance (Unifiable a) => Unifiable [a] where
  type Term [a] = LogicList a
  subst = genericSubst
  unify = genericUnify
  inject = genericInject
  extract = genericExtract

instance IsList (LogicList a) where
  type Item (LogicList a) = ValueOrVar a
  fromList [] = LogicNil
  fromList (x : xs) = LogicCons x (Value (fromList xs))

instance (Unifiable a, Unifiable b) => Unifiable (a, b) where
  type Term (a, b) = (ValueOrVar a, ValueOrVar b)
  subst = genericSubst
  unify = genericUnify
  inject = genericInject
  extract = genericExtract

instance Unifiable Int
instance Unifiable Bool
instance Unifiable Void
