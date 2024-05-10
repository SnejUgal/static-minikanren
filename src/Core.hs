{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Core (
  VarId,
  Term (..),
  subst',
  unify',
  inject',
  extract',
  apply,
  apply',
  State,
  empty,
  makeVariable,
  Logical (..),
) where

import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Kind (Type)
import Data.Maybe (fromMaybe)
import GHC.Exts (IsList (..))
import Unsafe.Coerce (unsafeCoerce)

newtype VarId a = VarId Int
  deriving (Show, Eq)

data Term a
  = Var (VarId a)
  | Value (Logic a)

deriving instance (Show (Logic a)) => Show (Term a)
deriving instance (Eq (Logic a)) => Eq (Term a)

instance (IsList (Logic a)) => IsList (Term a) where
  type Item (Term a) = Item (Logic a)
  fromList = Value . fromList

instance (Num (Logic a)) => Num (Term a) where
  fromInteger = Value . fromInteger

subst' :: (Logical a) => (forall x. VarId x -> Maybe (Term x)) -> Term a -> Term a
subst' k (Value x) = Value (subst k x)
subst' k x@(Var i) = fromMaybe x (k i)

apply :: (Logical a) => Subst -> Term a -> Term a
apply (Subst m) = subst' (\(VarId i) -> unsafeReconstructTerm <$> IntMap.lookup i m)

apply' :: (Logical a) => Term a -> State -> Term a
apply' var State{knownSubst} = apply knownSubst var

addSubst :: (Logical a) => (VarId a, Term a) -> State -> State
addSubst (VarId i, value) State{knownSubst = Subst m, ..} =
  State
    { knownSubst =
        Subst $
          IntMap.insert i (ErasedTerm value) $
            updateSomeValue <$> m
    , ..
    }
 where
  updateSomeValue (ErasedTerm x) =
    ErasedTerm (apply (Subst (IntMap.singleton i (ErasedTerm value))) x)

-- >>> unify' (Value (Pair (Var 0, )))
unify' :: (Logical a) => Term a -> Term a -> State -> Maybe State
unify' l r state@State{..} =
  case (apply knownSubst l, apply knownSubst r) of
    (Var x, Var y)
      | x == y -> Just state
    (Var x, r') -> Just (addSubst (x, r') state)
    (l', Var y) -> Just (addSubst (y, l') state)
    (Value l', Value r') -> unify l' r' state

inject' :: (Logical a) => a -> Term a
inject' = Value . inject

extract' :: (Logical a) => Term a -> Maybe a
extract' Var{} = Nothing
extract' (Value x) = extract x

data ErasedTerm where
  ErasedTerm :: (Logical a) => Term a -> ErasedTerm

unsafeReconstructTerm :: ErasedTerm -> Term a
unsafeReconstructTerm (ErasedTerm x) = unsafeCoerce x

newtype Subst = Subst (IntMap ErasedTerm)

data State = State
  { knownSubst :: !Subst
  , maxVarId :: !Int
  }

empty :: State
empty = State{knownSubst = Subst IntMap.empty, maxVarId = 0}

makeVariable :: State -> (State, Term a)
makeVariable State{maxVarId, ..} = (State{maxVarId = maxVarId + 1, ..}, Var (VarId maxVarId))

class Logical a where
  type Logic (a :: Type) = r | r -> a
  type Logic a = a

  subst :: (forall x. VarId x -> Maybe (Term x)) -> Logic a -> Logic a
  default subst :: (a ~ Logic a) => (forall x. VarId x -> Maybe (Term x)) -> Logic a -> Logic a
  subst _ = id

  unify :: Logic a -> Logic a -> State -> Maybe State
  default unify :: (Eq (Logic a)) => Logic a -> Logic a -> State -> Maybe State
  unify x y state
    | x == y = Just state
    | otherwise = Nothing

  inject :: a -> Logic a
  default inject :: (a ~ Logic a) => a -> Logic a
  inject = id

  extract :: Logic a -> Maybe a
  default extract :: (a ~ Logic a) => Logic a -> Maybe a
  extract = Just
