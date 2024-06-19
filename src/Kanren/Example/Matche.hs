{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Kanren.Example.Matche (example, eithero') where

import Control.Lens (Prism, from)
import Control.Lens.TH
import Data.Bifunctor (bimap)
import Data.Function ((&))
import Data.Tagged (Tagged)
import GHC.Generics (Generic)

import Kanren.Core
import Kanren.Goal
import Kanren.LogicalBase
import Kanren.Match
import Kanren.TH

eithero :: (Logical a, Logical b) => Term (Either a b) -> Goal ()
eithero =
  matche
    & on _LogicLeft (\_ -> return ())
    & on _LogicRight (\_ -> return ())

nestedo :: Term (Either (Either Int Bool) Int) -> Goal ()
nestedo =
  matche
    & on (_LogicLeft . _Value . _LogicLeft) (=== 42)
    & on (_LogicLeft . _Value . _LogicRight) (=== Value True)
    & on _LogicRight (=== 1729)

-- Exhaustive pattern-matching

eithero' :: (Logical a, Logical b) => Term (Either a b) -> Goal ()
eithero' =
  matche'
    & on' _LogicLeft' (\_ -> return ())
    & on' _LogicRight' (\_ -> return ())
    & enter'

nestedo' :: Term (Either (Either Int Bool) Int) -> Goal ()
nestedo' =
  matche'
    & on' (_LogicLeft' . _Value' . _LogicLeft') (=== 42)
    & on' (_LogicLeft' . _Value' . _LogicRight') (=== Value True)
    & on' _LogicRight' (=== 1729)
    & enter'

data Nat
  = Z
  | S Nat
  deriving (Show, Generic)

makeLogical ''Nat
makePrisms ''LogicNat

_Z' :: Prism (Tagged (z, s) LogicNat) (Tagged (z', s) LogicNat) (Tagged z ()) (Tagged z' ())
_Z' = from _Tagged . _LogicZ . _Tagged

_S' :: Prism (Tagged (z, s) LogicNat) (Tagged (z, s') LogicNat) (Tagged s (Term Nat)) (Tagged s' (Term Nat))
_S' = from _Tagged . _LogicS . _Tagged

natToInto :: Term Nat -> Term Int -> Goal ()
natToInto nat int =
  nat
    & ( matche'
          & on' _Z' (\() -> int === 0)
          & on' (_S' . _Value' . _Z') (\() -> int === 1)
          & on' (_S' . _Value' . _S' . _Value' . _Z') (\() -> int === 2)
          & on' (_S' . _Value' . _S' . _Value' . _S') (const failo) -- give up
          & enter'
      )

example :: IO ()
example = do
  putStrLn "eithero:"
  mapM_ print $ run (eithero @Int @Bool)

  putStrLn "\neithero':"
  mapM_ print $ run (eithero' @Int @Bool)

  putStrLn "\nnestedo:"
  mapM_ print $ extract' <$> run nestedo

  putStrLn "\nnestedo':"
  mapM_ print $ extract' <$> run nestedo'

  putStrLn "\nnatToInto:"
  mapM_ print $ bimap extract' extract' <$> run (uncurry natToInto)
