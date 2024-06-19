{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module Kanren.THSpec (spec) where

import Control.Lens.TH (makePrisms)
import Data.Function ((&))
import Data.Maybe (isJust, isNothing)
import GHC.Generics (Generic)
import Test.Hspec
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck (Arbitrary (arbitrary), frequency, label)

import Kanren.Core
import Kanren.LogicalBase ()
import Kanren.Match
import Kanren.TH

data Constructors
  = Simple
  | WithData Int
  | Char :@ Bool
  deriving (Eq, Show, Generic)

data Record a = Record
  { spam :: String
  , ham :: a
  }
  deriving (Generic)

data GADTLike where
  GADTLike :: Int -> GADTLike
  deriving (Generic)

data RecordGADTLike a where
  RecordGADTLike :: {gadtSpam :: a} -> RecordGADTLike a
  deriving (Generic)

data a ^ b = (:^) a b | b `Caret` a deriving (Generic)

newtype Newtype a = Newtype {runNewtype :: (a, a)} deriving (Generic)

data RecursiveA = RecursiveA Int RecursiveB deriving (Generic)
data RecursiveB = RecursiveB Bool RecursiveA deriving (Generic)

makeLogical ''Constructors
makeLogical ''Record
makeLogical ''GADTLike
makeLogical ''RecordGADTLike
makeLogical ''(^)
makeLogicType ''Newtype
makeLogicals [''RecursiveA, ''RecursiveB]

makePrisms ''LogicConstructors
makeExhaustivePrisms ''LogicConstructors

instance Arbitrary Constructors where
  arbitrary =
    frequency
      [ (1, pure Simple)
      , (20, WithData <$> arbitrary)
      , (30, (:@) <$> arbitrary <*> arbitrary)
      ]

ofTypeTerm :: Term a -> ()
ofTypeTerm = const ()

ofTypeLogic :: Logic a -> ()
ofTypeLogic = const ()

toConstr :: Constructors -> String
toConstr Simple = "Simple"
toConstr (WithData _) = "WithData"
toConstr (_ :@ _) = ":@"

spec :: Spec
spec = do
  describe "makeLogic" $ do
    it "generates proper constructors" $ do
      let _c :: LogicConstructors -> ()
          _c LogicSimple = ()
          _c (LogicWithData x) = ofTypeTerm x
          _c (x :?@ y) = ofTypeTerm x `seq` ofTypeTerm y
      let _r :: LogicRecord a -> ()
          _r LogicRecord{logicSpam = x, logicHam = y} =
            ofTypeTerm x `seq` ofTypeTerm y
      let _g :: LogicGADTLike -> ()
          _g (LogicGADTLike x) = ofTypeTerm x
      let _h :: LogicRecordGADTLike a -> ()
          _h LogicRecordGADTLike{logicGadtSpam = x} = ofTypeTerm x
      let _c :: (a ?^ b) -> ()
          _c (x :?^ y) = ofTypeTerm x `seq` ofTypeTerm y
          _c (x `LogicCaret` y) = ofTypeTerm x `seq` ofTypeTerm y
      let _n :: LogicNewtype a -> ()
          _n LogicNewtype{logicRunNewtype = x} = ofTypeLogic x
      let _a :: LogicRecursiveA -> ()
          _a (LogicRecursiveA x y) = ofTypeTerm x `seq` ofTypeTerm y
      let _b :: LogicRecursiveB -> ()
          _b (LogicRecursiveB x y) = ofTypeTerm x `seq` ofTypeTerm y

      return @IO ()

    it "generates proper exhaustive prisms" $ do
      let _ =
            matche'
              & on' _LogicSimple' return
              & on' _LogicWithData' (return . ofTypeTerm)
              & on' (.:?@!) (\(x, y) -> return (ofTypeTerm x `seq` ofTypeTerm y))
              & enter'

      return @IO ()

    prop "generates proper inject and extract" $
      \(x :: Constructors) ->
        label (toConstr x) $
          extract (inject x) == Just x

    prop "generated extract returns Nothing for partial values" $ do
      let (_, var) = makeVariable empty

      extract (LogicWithData var) `shouldSatisfy` isNothing
      extract (var :?@ Value True) `shouldSatisfy` isNothing

    prop "generates proper unify" $
      \(x :: Constructors) ->
        label (toConstr x) $
          unify (inject x) (inject x) empty `shouldSatisfy` isJust
