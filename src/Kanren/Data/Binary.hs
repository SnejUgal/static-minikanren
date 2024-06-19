{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

-- | This module implements binary numbers as described in the declarative pearl
-- “Pure, Declarative, and Constructive Arithmetic Relations” by O. Kiselyov
-- /et al/.
--
-- The paper is available at <https://okmij.org/ftp/Prolog/Arithm/arithm.pdf>
-- and the original implementation in Prolog is available at
-- <https://okmij.org/ftp/Prolog/Arithm/pure-bin-arithm.prl>.
module Kanren.Data.Binary (
  Bit (..),
  _O,
  _I,
  _O',
  _I',
  Binary,
  zeroo,
  poso,
  gtlo,
  binaryo,
  addo,
  subo,
  lesso,
  mulo,
  divo,
  logo,
  example,
) where

import Control.DeepSeq (NFData)
import Control.Lens.TH (makePrisms)
import Data.Bifunctor (bimap)
import Data.Function ((&))
import GHC.Generics (Generic)

import Kanren.Core
import Kanren.Goal
import Kanren.LogicalBase
import Kanren.Match
import Kanren.TH

data Bit = O | I deriving (Eq, Show, Generic, NFData)
instance Logical Bit
makePrisms ''Bit
makeExhaustivePrisms ''Bit

type Binary = [Bit]

instance Num Binary where
  fromInteger 0 = []
  fromInteger 1 = [I]
  fromInteger x | x > 1 = bit : fromInteger (x `div` 2)
   where
    bit
      | even x = O
      | otherwise = I
  fromInteger _ = error "Binary numbers cannot be negative"

  (+) = undefined
  (*) = undefined
  abs = id
  signum = undefined
  negate = undefined

-- | Check that the number is zero.
zeroo :: Term Binary -> Goal ()
zeroo n = n === inject' 0

-- | Check that the number is positive, i.e. greater than zero.
poso :: Term Binary -> Goal ()
poso n = do
  (x, xs) <- fresh
  n === Value (LogicCons x xs)

-- | Check that the number is greater than one (i.e. at least two).
--
-- The naming comes from the paper.
gtlo :: Term Binary -> Goal ()
gtlo n = do
  (x, y, ys) <- fresh
  n === Value (LogicCons x (Value (LogicCons y ys)))

{- FOURMOLU_DISABLE -}
-- | Generate valid binary numbers.
binaryo :: Term Binary -> Goal ()
binaryo = matche'
  & on' _LogicNil' return
  & on' _LogicCons' (\(b, bs) -> do
      b & (matche'
        & on' _I' return
        & on' _O' (\() -> poso bs)
        & enter')
      binaryo bs)
  & enter'
{- FOURMOLU_ENABLE -}

-- | Check that the first list is shorter than the second one.
lesslo :: Term Binary -> Term Binary -> Goal ()
lesslo n m =
  disjMany
    [ do
        zeroo n
        poso m
    , do
        n === inject' 1
        gtlo m
    , do
        (a, x, b, y) <- fresh
        n === Value (LogicCons a x)
        poso x
        m === Value (LogicCons b y)
        poso y
        lesslo x y
    ]

-- | Check that the lists have the same length.
samelo :: Term Binary -> Term Binary -> Goal ()
samelo n m =
  disjMany
    [ do
        zeroo n
        zeroo m
    , do
        n === inject' 1
        m === inject' 1
    , do
        (a, x, b, y) <- fresh
        n === Value (LogicCons a x)
        poso x
        m === Value (LogicCons b y)
        poso y
        samelo x y
    ]

-- | Check that the first list is shorter than the second one and at least of
-- the same length as the third list combined with the forth one.
--
-- Meaningfully, the part @[a]@ must be shorter than the whole @[b]@ and must
-- fit the result of multiplying @[c]@ with @[d]@, but here we're just concerned
-- with the lengths of the lists.
lessl3o :: Term Binary -> Term Binary -> Term Binary -> Term Binary -> Goal ()
lessl3o q c a b =
  disjMany
    [ do
        zeroo q
        poso c
    , do
        (a0, a1, a2, a3, x, (y, z)) <- fresh
        q === Value (LogicCons a0 x)
        c === Value (LogicCons a1 y)
        disjMany
          [ do
              zeroo a
              b === Value (LogicCons a2 z)
              lessl3o x y z (inject' 0)
          , do
              a === Value (LogicCons a3 z)
              lessl3o x y z b
          ]
    ]

appendo :: (Logical a) => Term [a] -> Term [a] -> Term [a] -> Goal ()
appendo xs ys zs =
  disjMany
    [ do
        xs === inject' []
        ys === zs
    , do
        (x, xs', zs') <- fresh
        xs === Value (LogicCons x xs')
        zs === Value (LogicCons x zs')
        appendo xs' ys zs'
    ]

-- | A one-bit full adder.
full1Addero :: Term Bit -> Term Bit -> Term Bit -> Term Bit -> Term Bit -> Goal ()
full1Addero carryIn a b s carryOut =
  disjMany
    [ do
        carryIn === Value O
        disjMany
          [ do
              a === Value O
              conde
                [ [b === Value O, s === Value O, carryOut === Value O]
                , [b === Value I, s === Value I, carryOut === Value O]
                ]
          , do
              a === Value I
              conde
                [ [b === Value O, s === Value I, carryOut === Value O]
                , [b === Value I, s === Value O, carryOut === Value I]
                ]
          ]
    , do
        carryIn === Value I
        disjMany
          [ do
              a === Value O
              conde
                [ [b === Value O, s === Value I, carryOut === Value O]
                , [b === Value I, s === Value O, carryOut === Value I]
                ]
          , do
              a === Value I
              conde
                [ [b === Value O, s === Value O, carryOut === Value I]
                , [b === Value I, s === Value I, carryOut === Value I]
                ]
          ]
    ]

-- | A full adder for numbers of arbitrary lengths.
fullNAddero :: Term Bit -> Term Binary -> Term Binary -> Term Binary -> Goal ()
fullNAddero carryIn a b r =
  disjMany
    [ do
        carryIn === Value O
        zeroo b
        a === r
    , do
        carryIn === Value O
        zeroo a
        b === r
        poso b
    , do
        carryIn === Value I
        zeroo b
        fullNAddero (Value O) a (inject' 1) r
    , do
        carryIn === Value I
        zeroo a
        poso b
        fullNAddero (Value O) (inject' 1) b r
    , do
        a === inject' 1
        b === inject' 1
        (d, c) <- fresh
        r === Value (LogicCons d (Value (LogicCons c (Value LogicNil))))
        full1Addero carryIn (Value I) (Value I) d c
    , do
        a === inject' 1
        genFullNAddero carryIn a b r
    , do
        b === inject' 1
        gtlo a
        gtlo r
        fullNAddero carryIn (inject' 1) a r
    , do
        gtlo a
        genFullNAddero carryIn a b r
    ]

genFullNAddero :: Term Bit -> Term Binary -> Term Binary -> Term Binary -> Goal ()
genFullNAddero carryIn n m r = do
  (a, b, c, e, x, (y, z)) <- fresh
  n === Value (LogicCons a x)
  m === Value (LogicCons b y)
  poso y
  r === Value (LogicCons c z)
  poso z
  full1Addero carryIn a b c e
  fullNAddero e x y z

-- | Calculate the sum @c@ of two numbers @a@ and @b@.
--
-- >>> extract' <$> run (addo (inject' 3) (inject' 5))
-- [Just [O,O,O,I]]
--
-- One can turn it around to subtract from a number:
--
-- >>> extract' <$> run (\b -> addo (inject' 2) b (inject' 8))
-- [Just [O,I,I]]
--
-- When both summands are unknown, every possible pair will be enumerated.
--
-- >>> bimap extract' extract' <$> run (\(a, b) -> addo a b (inject' 2))
-- [(Just [O,I],Just []),(Just [],Just [O,I]),(Just [I],Just [I])]
--
-- If one of the summands is greater than the sum, the relation will produce no
-- results.
--
-- >>> run (\a -> addo a (inject' 10) (inject' 3))
-- []
--
-- The implementation of @add@ is discussed in section 4 of the paper.
addo
  :: Term Binary
  -- ^ @a@, the first summand
  -> Term Binary
  -- ^ @b@, the second summand
  -> Term Binary
  -- ^ @c@, the sum
  -> Goal ()
addo = fullNAddero (inject' O)

-- | Calculate the difference @c@ of two numbers @a@ and @b@. This is just
-- 'addo', but with parameters in different order.
subo
  :: Term Binary
  -- ^ @a@, the minuend
  -> Term Binary
  -- ^ @b@, the subtrahend
  -> Term Binary
  -- ^ @c@, the difference
  -> Goal ()
subo a b c = addo b c a

-- | Check that @a@ is strictly less than @b@. Otherwise, the goal fails.
--
-- >>> run (\() -> lesso (inject' 3) (inject' 4))
-- [()]
-- >>> run (\() -> lesso (inject' 3) (inject' 2))
-- []
--
-- One can turn this relation around to generate numbers less or greater than a
-- given one.
--
-- >>> extract' <$> run (\x -> lesso x (inject' 4))
-- [Just [],Just [I],Just [I,I],Just [O,I]]
-- >>> take 5 $ extract' <$> run (\x -> lesso (inject' 4) x)
-- [Just [I,O,I],Just [O,I,I],Just [I,I,I],Just [O,O,O,I],Just [I,O,O,I]]
lesso
  :: Term Binary
  -- ^ @a@, the lesser number
  -> Term Binary
  -- ^ @b@, the greater number
  -> Goal ()
lesso a b =
  disjMany
    [ do
        lesslo a b
    , do
        samelo a b
        x <- fresh
        poso x
        addo a x b
    ]

-- | Calculate the product @c@ of two numbers @a@ and @b@.
--
-- >>> extract' <$> run (mulo (inject' 3) (inject' 4))
-- [Just [O,O,I,I]]
--
-- One can turn this around to factor a given number.
--
-- >>> extract' <$> run (\a -> mulo a (inject' 2) (inject' 12))
-- [Just [O,I,I]]
-- >>> bimap extract' extract' <$> run (\(a, b) -> mulo a b (inject' 4))
-- [(Just [I],Just [O,O,I]),(Just [O,I],Just [O,I]),(Just [O,O,I],Just [I])]
--
-- The goal will fail if any multiplier is not a factor of the product.
--
-- >>> run (\a -> mulo a (inject' 5) (inject' 7))
-- []
--
-- The implementation of @mul@ is discussed in section 5 of the paper.
mulo
  :: Term Binary
  -- ^ @a@, the first multiplier
  -> Term Binary
  -- ^ @b@, the second multiplier
  -> Term Binary
  -- ^ @c@, the product
  -> Goal ()
mulo a b c =
  disjMany
    [ do
        zeroo a
        zeroo c
    , do
        poso a
        zeroo b
        zeroo c
    , do
        a === inject' 1
        poso b
        b === c
    , do
        gtlo a
        b === inject' 1
        a === c
    , do
        (x, z) <- fresh
        a === Value (LogicCons (Value O) x)
        poso x
        c === Value (LogicCons (Value O) z)
        poso z
        gtlo b
        mulo x b z
    , do
        (x, y) <- fresh
        a === Value (LogicCons (Value I) x)
        poso x
        b === Value (LogicCons (Value O) y)
        poso y
        mulo b a c
    , do
        (x, y) <- fresh
        a === Value (LogicCons (Value I) x)
        poso x
        b === Value (LogicCons (Value I) y)
        poso y

        q <- fresh
        lessl3o q c a b
        mulo x b q
        addo (Value (LogicCons (Value O) q)) b c
    ]

-- | Calculate the quotient @q@ and remainder @r@ of dividing @n@ by @m@.
--
-- >>> bimap extract' extract' <$> run (\(q, r) -> divo (inject' 17) (inject' 5) q r)
-- [(Just [I,I],Just [O,I])]
--
-- One can turn this around to find divisors of a number.
--
-- >>> extract' <$> run (\m -> fresh >>= \q -> divo (inject' 12) m q (inject' 0))
-- [Just [O,O,I,I],Just [I],Just [I,I],Just [O,I,I],Just [O,I],Just [O,O,I]]
--
-- The implementation of @div@ is discussed in section 6 of the paper.
divo
  :: Term Binary
  -- ^ @n@, the dividend
  -> Term Binary
  -- ^ @m@, the divisor
  -> Term Binary
  -- ^ @q@, the quotient
  -> Term Binary
  -- ^ @r@, the remainder
  -> Goal ()
divo n m q r =
  disjMany
    [ do
        n === r
        zeroo q
        lesso n m
    , do
        q === inject' 1
        samelo n m
        addo r m n
        lesso r m
    , do
        lesslo m n
        lesso r m
        poso q

        (n1, n2, q1, q2, q2m, (q2mr, rr, r1)) <- fresh
        splito n r n1 n2
        splito q r q1 q2
        disjMany
          [ do
              zeroo n1
              zeroo q1
              subo n2 r q2m
              mulo q2 m q2m
          , do
              poso n1
              mulo q2 m q2m
              addo q2m r q2mr
              subo q2mr n2 rr
              splito rr r r1 (inject' 0)
              divo n1 m q1 r1
          ]
    ]

-- | Split @n@ into @n1@ and @n2@ such that @n = 2^(length r + 1) * n1 + n2@.
splito :: Term Binary -> Term Binary -> Term Binary -> Term Binary -> Goal ()
splito n r n1 n2 =
  disjMany
    [ do
        zeroo n
        zeroo n1
        zeroo n2
    , do
        (b, n') <- fresh
        n === Value (LogicCons (Value O) (Value (LogicCons b n')))
        zeroo r
        n1 === Value (LogicCons b n')
        zeroo n2
    , do
        n' <- fresh
        n === Value (LogicCons (Value I) n')
        zeroo r
        n1 === n'
        n2 === inject' 1
    , do
        (b, n', a, r') <- fresh
        n === Value (LogicCons (Value O) (Value (LogicCons b n')))
        r === Value (LogicCons a r')
        zeroo n2
        splito (Value (LogicCons b n')) r' n1 (inject' 0)
    , do
        (n', a, r') <- fresh
        n === Value (LogicCons (Value I) n')
        r === Value (LogicCons a r')
        n2 === inject' 1
        splito n' r' n1 (inject' 0)
    , do
        (b, n', a, r', n2') <- fresh
        n === Value (LogicCons b n')
        r === Value (LogicCons a r')
        n2 === Value (LogicCons b n2')
        poso n2'
        splito n' r' n1 n2'
    ]

-- | Calculate @n = (b + 1)^q@, where @b + 1@ is a power of two.
exp2o :: Term Binary -> Term Binary -> Term Binary -> Goal ()
exp2o n b q =
  disjMany
    [ do
        n === inject' 1
        zeroo q
    , do
        gtlo n
        q === inject' 1
        _n2 <- fresh
        splito n b (inject' 1) _n2
    , do
        (q1, b2) <- fresh
        q === Value (LogicCons (Value O) q1)
        poso q1
        lesslo b n
        appendo b (Value (LogicCons (Value I) b)) b2
        exp2o n b2 q1
    , do
        (q1, n1, b2, _n2) <- fresh
        q === Value (LogicCons (Value I) q1)
        poso q1
        poso n1
        splito n b n1 _n2
        appendo b (Value (LogicCons (Value I) b)) b2
        exp2o n1 b2 q1
    ]

-- | Calculate @nq = n ^ q@.
repeatedMulo :: Term Binary -> Term Binary -> Term Binary -> Goal ()
repeatedMulo n q nq =
  disjMany
    [ do
        poso n
        zeroo q
        nq === inject' 1
    , do
        q === inject' 1
        n === nq
    , do
        gtlo q
        (q1, nq1) <- fresh
        addo q1 (inject' 1) q
        repeatedMulo n q1 nq1
        mulo nq1 n nq
    ]

-- | Calculate discrete logarithm @q@ of a number @n@ in base @b@, perhaps with
-- some remainder @r@.
--
-- >>> bimap extract' extract' <$> run (\(q, r) -> logo (inject' 9) (inject' 3) q r)
-- [(Just [O,I],Just [])]
-- >>> bimap extract' extract' <$> run (\(q, r) -> logo (inject' 15) (inject' 3) q r)
-- [(Just [O,I],Just [0,I,I])]
--
-- One can turn this around to find the number @b@ raised to some power @q@:
--
-- >>> extract' <$> run (\n -> logo n (inject' 5) (inject' 2) (inject' 0))
-- [Just [I,O,O,I,I]]
--
-- or to find the @q@-th root of @n@:
--
-- >>> extract' <$> run (\b -> logo (inject' 8) b (inject' 3) (inject' 0))
-- [Just [O,I]]
--
-- If you want to enumerate solutions to @logo n b q r@, you probably shouldn't
-- go beyond the first 16 solutions without an OOM killer.
--
-- The original implementation of this relation in Prolog can be found at
-- <https://okmij.org/ftp/Prolog/Arithm/pure-bin-arithm.prl>. Although the paper
-- mentions this relation in section 6, it does not discuss its implementation
-- in detail.
logo
  :: Term Binary
  -- ^ @n@, of which to calculate the logarithm
  -> Term Binary
  -- ^ @b@, the base
  -> Term Binary
  -- ^ @q@, the logarithm
  -> Term Binary
  -- ^ @r@, the remainder
  -> Goal ()
logo n b q r =
  disjMany
    [ do
        -- n = b^0 + 0, b > 0
        n === inject' 1
        poso b
        zeroo q
        zeroo r
    , do
        -- n = b^0 + r, r > 0
        zeroo q
        lesso n b
        poso r
        addo r (inject' 1) n
    , do
        -- n = b^1 + r, b >= 2
        q === inject' 1
        gtlo b
        samelo n b
        addo r b n
    , do
        -- n = 1^q + r, q > 0
        b === inject' 1
        poso q
        addo r (inject' 1) n
    , do
        -- n = 0^q + r, q > 0
        zeroo b
        poso q
        n === r
    , do
        -- n = 2^q + r, n >= 4
        b === inject' 2
        (_b1, _b2, n1) <- fresh
        poso n1
        n === Value (LogicCons _b1 (Value (LogicCons _b2 n1)))
        exp2o n (inject' 0) q
        _r1 <- fresh
        splito n n1 _r1 r
    , do
        -- n = b^q + r, b >= 3
        (b1, b2, b3, br) <- fresh
        disjMany
          [ b === inject' 3
          , b === Value (LogicCons b1 (Value (LogicCons b2 (Value (LogicCons b3 br)))))
          ]
        lesslo b n

        (bw1, bw, nw1, nw, ql, (ql1, _r)) <- fresh
        exp2o b (inject' 0) bw1
        addo bw1 (inject' 1) bw
        lesslo q n

        (q1, bwq1) <- fresh
        addo q (inject' 1) q1
        mulo bw q1 bwq1
        lesso nw1 bwq1

        exp2o n (inject' 0) nw1
        addo nw1 (inject' 1) nw
        divo nw bw ql1 _r
        addo ql (inject' 1) ql1
        disjMany [samelo q ql, lesslo ql q]

        (bql, qh, _r', qdh, qd) <- fresh
        repeatedMulo b ql bql
        divo nw bw1 qh _r'
        addo ql qdh qh
        addo ql qd q
        disjMany [qd === qdh, lesso qd qdh]

        (bqd, bq, bq1) <- fresh
        repeatedMulo b qd bqd
        mulo bql bqd bq
        mulo b bq bq1
        addo bq r n
        lesso n bq1
    ]

example :: IO ()
example = do
  putStrLn "addo 3 5 x:"
  mapM_ print $ extract' <$> run (addo (inject' 3) (inject' 5))

  putStrLn "\nmulo 3 4 x:"
  mapM_ print $ extract' <$> run (mulo (inject' 3) (inject' 4))

  putStrLn "\ndivo 15 4 q r:"
  mapM_ print $ bimap extract' extract' <$> run (uncurry (divo (inject' 15) (inject' 4)))

  let exps =
        [ (b, p, run (\n -> logo n (inject' (fromInteger b)) (inject' (fromInteger p)) (inject' 0)))
        | b <- [1 .. 3]
        , p <- [1 .. 6]
        ]
  mapM_
    ( \(b, p, bp) -> do
        putStrLn ("\nlogo n " ++ show b ++ " " ++ show p ++ " 0:")
        mapM_ print (extract' <$> bp)
    )
    exps
