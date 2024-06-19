{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

-- | The @matche@ for Haskell. Comes in non-exhaustive and, most importantly,
-- exhaustive versions.
module Kanren.Match (
  -- * Non-exhaustive pattern matching

  -- | Pattern matching in this library syntactially looks similar to the one
  -- from the @total@ package and is based on 'Prism's, though the mechanics
  -- differ. Let's take a look at an example.
  --
  -- > data Expr
  -- >   = Variable String
  -- >   | Abstraction String Expr
  -- >   | Apply Expr Expr
  -- >   deriving (Generic)
  -- > makeLogic ''Expr
  -- > makePrisms ''LogicExpr
  -- >
  -- > expro :: Term Expr -> Goal ()
  -- > expro = matche
  -- >   & on _LogicVariable (\_var -> return ())
  -- >   & on _LogicAbstraction (\(_var, body) -> expro body)
  --
  -- After defining our data type, we derived its logic type using
  -- 'TH.makeLogic', and then generated prisms for the logic type using
  -- 'Control.Lens.TH.makePrisms' from the @lens@ package. The prisms are
  -- crucial to enable pattern matching.
  --
  -- Two functions are used for pattern matching: 'matche' and 'on'. They are
  -- composed using 'Data.Function.&' so that the code looks similar to
  -- the built-in @case@ expression.
  --
  -- At the very top, we use 'matche'. Then, for every case we want to consider,
  -- we use 'on' and provide a prism — the left-hand side of the arm — and a
  -- function — the right-hand side of the arm. If the value matches the
  -- pattern, the function is applied to the data stored inside the variant.
  --
  -- When pattern-matching on a term, every arm will be tried. Results from each
  -- arm will be combined using 'disj'unction. This is just like how @matche@
  -- from @faster-minikanren@ behaves.
  --
  -- >>> mapM_ print (take 3 (run expro))
  -- Value (LogicVariable (Var (VarId 1)))
  -- Value (LogicAbstraction (Var (VarId 1)) (Value (LogicVariable (..))))
  -- Value (LogicAbstraction (Var (VarId 1)) (Value (LogicAbstraction ...)))
  --
  -- >>> run (\() -> expro (inject' (Variable "foo")))
  -- [()]
  -- >>> run (\() -> expro (inject' (Apply (Variable "f") (Variable "x"))))
  -- []
  --
  -- (note that @expro@ deliberately doesn't include a case for @Apply@.)
  --
  -- How does this actually work? Remember that 'Data.Function.&' just
  -- swaps the function and its argument, so @expro@ is equivalent to
  --
  -- > on _LogicAbstraction (\(_var, body) -> expro body)
  -- >    (on _LogicVariable (\_var -> return ())
  -- >        matche)
  --
  -- One can now clearly see that 'on' takes a third argument in which other
  -- cases are considered. It takes a forth argument too — the value to match
  -- on. When you provide that value, 'on' will try to match it with the given
  -- pattern, and apply the given function if possible. 'on' will also apply
  -- this value to the remaning cases and take a 'disj'unction. The 'matche'
  -- at the end is just @const failo@.
  --
  -- Since 'on' is expected to be used with 'Data.Function.&', it will take
  -- special care to test cases in the order they will appear in the source
  -- code. This means that you can list cases in the natural order from
  -- simple on the top to complex on the bottom and the code will work as
  -- expected.
  --
  -- 'on' and 'matche' together make for non-exhaustive pattern matching. As you
  -- have already seen, @expro@ in the above examples misses a branch for the
  -- @Apply@. This is perfectly safe, since non-handled variants will just lead
  -- to contradiction. However, it may be desirable to perform an exhaustive
  -- pattern matching — see [the next section](#g:exhaustive) for that.
  --
  -- Non-exhaustive pattern matching also lets you consider the same variant
  -- twice or more. The results will be combined in the usual way.
  --
  -- >>> :{
  --   extract' <$> run (matche
  --     & on _LogicVariable (\x -> x === inject' "x")
  --     & on _LogicVariable (\x -> x === inject' "y"))
  -- :}
  -- [Just (Variable "x"),Just (Variable "y")]
  --
  -- If a variant contains just a single field, it is possible to perform nested
  -- pattern matching. All it takes is to compose two prisms with '_Value' in
  -- between:
  --
  -- >>> :{
  --   extract' <$> run (matche
  --     & on (_LogicLeft . _Value . _LogicVariable) (\x -> x === inject' "x")
  --     & on (_LogicRight . _Value . _LogicVariable) (\x -> x === inject' "y"))
  -- :}
  -- [Just (Left (Variable "x")),Just (Right (Variable "y"))]
  --
  -- The '_Value' here is just the glue between the focus of the left prism,
  -- which is a @'Term' a@, and the source of the right prism, which is a
  -- @'Logic' a@.
  --
  -- Note that in the very first example, @expro@ is a function with one
  -- parameter, but its equation does not include it on the left side. That's
  -- because the whole @matche & ...@ expression is a function, and this is nice
  -- when you want to match on the last parameter in the relation. If this is
  -- not applicable in your case, you might want to use the following syntax:
  --
  -- > x & (matche
  -- >   & on ...)
  --
  -- Finally, the @"LogicalBase"@ module, which provides 'Logical' instances for
  -- @base@ types, also provides prisms for their logical representations for
  -- the purposes of pattern matching.
  on,
  matche,
  _Value,

  -- * Exhaustive pattern matching #exhaustive#

  -- | While lispers may be fine with pattern matching as described in the
  -- previous section, we haskellers love exhaustive pattern matching, and it
  -- would be sad if we'd have to give up on it when writing relational programs
  -- in Haskell. So this module also provides a variation on pattern matching
  -- with compile-time exhaustiveness check. It looks quite similar to the
  -- non-exhaustive version:
  --
  -- > expro' :: Term Expr -> Goal ()
  -- > expro' = matche'
  -- >   & on' _LogicVariable' (\_var -> return ())
  -- >   & on' _LogicAbstraction' (\(_var, body) -> expro body)
  -- >   & on' _LogicApply' (\(function, argument) -> do
  -- >       expro function
  -- >       expro argument)
  -- >   & enter'
  --
  -- 'matche' becomes 'matche'', 'on' becomes 'on'', and 'enter'' comes on the
  -- scene. We also need to use a bit different prisms, which get an apostrophe
  -- at the end as well. For now we'll just assume that we already have them:
  --
  -- >>> mapM_ print (take 3 (run expro'))
  -- Value (LogicVariable ...)
  -- Value (LogicApply ...)
  -- Value (LogicAbstraction ...)
  --
  -- This works, but we are more interested in the case when we forgot a case
  -- and would like to get a compile-time error.
  --
  -- >>> :{
  --   run (matche'
  --     & on' _LogicVariable' (\_var -> return ())
  --     & on' _LogicAbstraction' (\(_var, body) -> expro body)
  --     & enter')
  -- :}
  -- <interactive>:2:6: error: [GHC-39999]
  --  • Ambiguous type variable ‘ap0’ arising from a use of ‘matche'’
  --    prevents the constraint ‘(Exhausted ap0)’ from being solved.
  --
  -- Indeed, our program fails to compile with an error so easy to understand
  -- we'll spend the next few paragraphs explaining it.
  --
  -- The magic that allows us to perform the exhaustiveness check is in the new
  -- prisms. They have the following type:
  --
  -- > ExhaustivePrism (Logic s) (…, c, …) (…, c', …) a c c'
  --
  -- …which is actually just an alias for the more verbose type
  --
  -- > Prism (Tagged (…, c , …) (Logic s))
  -- >       (Tagged (…, c', …) (Logic s))
  -- >       (Tagged c  a)
  -- >       (Tagged c' a)
  --
  -- The source type is now 'Tagged' with a tuple that contains a variable for
  -- each variant of the type. The focus is also 'Tagged' with the variable for
  -- the variant that this prism focuses on. Take a look at @_LogicVariable'@:
  --
  -- > _LogicVariable' :: ExhaustivePrism
  --     LogicExpr (v, ab, ap) (v', ab, ap)
  --     (Term String) v v'
  -- > _LogicVariable' = from _Tagged . _LogicVariable . _Tagged
  --
  -- These new prisms are easily implemented using regular prisms and the
  -- '_Tagged' isomorphism (provided by this module). It should be possible to
  -- generate them automatically, but this is not implemented yet.
  --
  -- In its type signature, 'on'' instantiates the type variable @c@ to
  -- @Remaining@ and @c'@ to @Checked@. The @Checked@ tag will be passed on to
  -- the remaining cases (and @Remaining will propagate back to previous cases).
  -- Therefore, the type checker will infer the following tags for each case
  -- (remember that 'Data.Function.&' is reverse application, so the
  -- exhaustiveness check happens bottom-up):
  --
  -- > matche'
  -- >   & on' _LogicVariable' …    -- (  Checked,   Checked, Checked)
  -- >   & on' _LogicAbstraction' … -- (Remaining,   Checked, Checked)
  -- >   & on' _LogicApply' …       -- (Remaining, Remaining, Checked)
  -- >   & enter'
  --
  -- Now, the job of 'matche'' now is to check that the tags it receives are all
  -- @Checked@. This is done using the private @Exhausted@ type class. It has
  -- instances for @Checked@ and tuples consisting of @Exhausted@ types.
  --
  -- While these tags are nice, they need to come from somewhere, but 'Term's
  -- don't have them. To solve this problem, we introduce 'enter'' which
  -- attaches tags to the term being matched. The 'enter'' has to be put below
  -- all cases.
  --
  -- The question now is, what happens when we miss a case? For the forgotten
  -- variant, the type checker will not be able to infer the concrete tag.
  -- When the tags arrive at 'matche'', the type checker will check for the
  -- @Exhausted@ constraint and fail, because it does not know if this
  -- constraint is satisfied for the unsolved type variable. Hence the compiler
  -- error we saw previously.
  --
  -- > matche'
  -- >   & on' _LogicVariable' …    -- (  Checked,   Checked, ap)
  -- >   & on' _LogicAbstraction' … -- (Remaining,   Checked, ap)
  -- >   & enter'                   -- (Remaining, Remaining, ap)
  --
  -- The exhaustive version of pattern matching also support nested patterns.
  -- Just like with non-exhaustive pattern matching, two prisms need to composed
  -- with '_Value'' in between.
  --
  -- > matche'
  -- >   & on' _LogicLeft' (\x -> x === Value False)
  -- >   & on' _LogicRight' . _Value' . _LogicJust' (\x -> x === Value 42)
  -- >   & on' _LogicRight' . _Value' . _LogicNothing' (\() -> failo)
  -- >   & enter'
  --
  -- In this example, the tags will have the form @(left, (nothing, just))@. You
  -- don't need to use nested patterns, but if you do, you have to enumerate all
  -- possible subcases as well. This works nicely with recursive types too.
  --
  -- Unlike non-exhaustive pattern matching, the exhaustive version explicitly
  -- disallows visiting the same variant twice. Although checking an already
  -- checked case wouldn't hurt, it doesn't play nicely with nested patterns.
  --
  -- The @"LogicalBase"@ provides prisms for exhaustive pattern matching too.
  enter',
  on',
  matche',
  ExhaustivePrism,
  _Tagged,
  _Value',
) where

import Control.Lens (
  Iso,
  Prism,
  Prism',
  from,
  iso,
  prism',
  review,
  reviewing,
 )
import Data.Tagged (Tagged (Tagged, unTagged))

import Kanren.Core
import Kanren.Goal

-- | One case for non-exhaustive pattern matching.
--
-- Although we try to match on a 'Term', the prism only need to operate on
-- a 'Logic' type.
--
-- In case when the value being match is unknown yet, 'on' must be able to
-- construct this value from the pattern — hence the @'Fresh' v@ constraint. It
-- should just work though since 'Fresh' has instances for tuples, and prisms'
-- foci are tuples too.
on
  :: (Logical a, Fresh v)
  => Prism' (Logic a) v
  -- ^ The pattern
  -> (v -> Goal x)
  -- ^ The handler
  -> (Term a -> Goal x)
  -- ^ Remaining cases
  -> Term a
  -- ^ Value being matched
  -> Goal x
on p f g x = disj (g x) $ do
  vars <- fresh
  x === Value (review p vars)
  f vars

-- | Finalize non-exhaustive pattern matching.
matche :: Term a -> Goal x
matche = const failo

-- | Focus on the logical value inside a term.
--
-- This prism aids nested pattern matching. You might expect that, since
-- regular prisms can be easily composed, say
-- @'Control.Lens.Prism._Just' . 'Control.Lens.Prism._Left'@, then
-- @'LogicalBase._LogicJust' . 'Logicalbase._LogicLeft'@ should also work.
-- However, this is not the case since the types are slightly different:
--
-- > _LogicJust :: Prism' (Logic (Maybe (Either a b))) (Term (Either a b))
-- > _LogicLeft :: Prism'                             (Logic (Either a b)) (Term a)
--
-- Hence, we need one more prism between 'LogicalBase._LogicJust' and
-- 'LogicalBase._LogicLeft' for the types to match. This prism is '_Value'.
_Value :: Prism' (Term a) (Logic a)
_Value = prism' Value $ \case
  Value x -> Just x
  Var _ -> Nothing

type Matched m a = Tagged m (Term a)

data Remaining
data Checked

class Exhausted a
instance Exhausted Checked
instance (Exhausted a, Exhausted b) => Exhausted (a, b)
instance (Exhausted a, Exhausted b, Exhausted c) => Exhausted (a, b, c)
instance
  (Exhausted a, Exhausted b, Exhausted c, Exhausted d)
  => Exhausted (a, b, c, d)

-- | A prism which is suitable for exhaustive pattern matching.
--
-- Although the type definition might allow changing the type of the focus, this
-- is not neccesary for exhaustive pattern matching and so not covered here.
type ExhaustivePrism s m m' a t t' =
  Prism (Tagged m s) (Tagged m' s) (Tagged t a) (Tagged t' a)

-- | Begin exhaustive pattern matching by attaching initial tags to the term.
-- Do keep in mind that these tags do not exist at runtime.
enter' :: (Matched m a -> Goal x) -> Term a -> Goal x
enter' f = delay . f . Tagged

-- | One case for exhaustive pattern matching.
--
-- Exhaustive pattern matching requires special prisms which know of all
-- possible variants and can mark a variant as checked. See the guide above for
-- details.
--
-- @Remaining@ and @Checked@ are private types on purpose.
on'
  :: (Logical a, Fresh v)
  => ExhaustivePrism (Logic a) m m' v Remaining Checked
  -- ^ The pattern, which also participates in the exhaustiveness check
  -> (v -> Goal x)
  -- ^ The handler
  -> (Matched m' a -> Goal x)
  -- ^ Remaining cases
  -> Matched m a
  -- ^ Value being matched
  -> Goal x
on' p f g (Tagged x) = disj (g (Tagged x)) $ do
  vars <- fresh
  let Tagged value = review (reviewing p) (Tagged vars)
  x === Value value
  f vars

-- | Finalize exhaustive pattern matching.
--
-- The @Exhausted m@ constraint checks that @m@ is composed only of @Checked@
-- tags.
--
-- > instance Exhaustive Checked
-- > instance (Exhaustive a, Exhaustive b) => Exhaustive (a, b)
-- > ...
matche' :: (Exhausted m) => Matched m a -> Goal x
matche' = const failo

-- | The isomorphism for 'Tagged', useful to implement prisms for exhaustive
-- pattern matching.
--
-- > _LogicJust' :: Prism
-- >   (Tagged (nothing, just ) (Maybe a ))
-- >   (Tagged (nothing, just') (Maybe a'))
-- >   (Tagged just  (Term a ))
-- >   (Tagged just' (Term a'))
-- > _LogicJust' = from _Tagged . _LogicJust . _Tagged
_Tagged :: Iso b b' (Tagged s b) (Tagged s' b')
_Tagged = iso Tagged unTagged

-- | Focus on the logical value inside a term.
--
-- This prism serves the same purpose as '_Value', but is adapted for exhaustive
-- pattern matching.
_Value' :: ExhaustivePrism (Term a) m m' (Logic a) m m'
_Value' = from _Tagged . _Value . _Tagged
