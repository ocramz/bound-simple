{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DerivingStrategies #-}
{-# language DeriveAnyClass #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# language CPP #-}
{-# options_ghc -Wno-unused-top-binds #-}
-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2013 Edward Kmett
--                (C) 2021 Marco Zocca (ocramz)
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  ocramz
-- Stability   :  experimental
-- Portability :  portable
--
-- 'Scope' is to be used inside of the definition of binders.
--
-- A lightweight implementation of 'bound'. Provides much of the functionality of Bound.Scope.Simple, without the large dependency footprint.
--
-- = Example
--
-- The 'whnf' function in this example shows how to beta-reduce a term of the untyped lambda calculus, as well as all the requisite setup needed by the library.
--
-- Note : the Show instance of Exp depends on its Show1 instance (since Exp has one type parameter), which can be derived 'Generically' thanks to DerivingVia. This works on most recent versions of GHC (>= 8.6.1).
--
-- @
-- {-# LANGUAGE DeriveFunctor #-}
-- {-# LANGUAGE DeriveFoldable #-}
-- {-# LANGUAGE DeriveTraversable #-}
--
-- import Bound.Simple (Scope, Bound(..), abstract1, instantiate1)
-- import Data.Functor.Classes.Generic (Generically(..))
-- 
-- import GHC.Generics (Generic1)
--
-- infixl 9 :\@
-- data Exp a = V a | Exp a :@ Exp a | Lam (Scope () Exp a)
--   deriving (Show, Functor, Foldable, Traversable, Generic1)
--   deriving (Show1) via Generically Exp
--
-- instance Applicative Exp where pure = V; k \<*\> m = ap k m
--
-- instance Monad Exp where
--   return = V
--   V a      >>= f = f a
--   (x :\@ y) >>= f = (x >>= f) :\@ (y >>= f)
--   Lam e    >>= f = Lam (e '>>>=' f)
--
-- lam :: Eq a => a -> Exp a -> Exp a
-- lam v b = Lam ('abstract1' v b)
--
-- whnf :: Exp a -> Exp a
-- whnf (e1 \:\@ e2) = case whnf e1 of
--   Lam b -> whnf ('instantiate1' e2 b)
--   f'    -> f' :\@ e2
-- whnf e = e
--
-- main :: IO ()
-- main = do
--   let term = lam 'x' (V 'x') :\@ V 'y'
--   print term         -- Lam (Scope (V (B ()))) :\@ V 'y'
--   print $ whnf term  -- V 'y'
-- @
----------------------------------------------------------------------------


module Bound.Simple (Bound(..), Scope, Var
  -- * Abstraction
  , abstract, abstract1
  -- * Instantiation
  , instantiate, instantiate1
  , bindings
  , hoistScope
  -- * Utils
  , Generically(..)
  ) where

import Control.Monad (ap, liftM)
import Control.Monad.Trans.Class (MonadTrans(..))
import Data.Functor.Classes (Show2(..), Show1(..), showsUnaryWith, showsPrec1, liftShowsPrec2, Eq2(..), Eq1(..), eq1, liftEq, liftEq2)
import GHC.Generics (Generic1)
import Data.Functor.Classes.Generic (Generically(..))

-- infixl 9 :@
-- data Exp a = V a | Exp a :@ Exp a | Lam (Scope () Exp a)
--   deriving (Show, Functor,Foldable,Traversable, Generic1)
--   deriving (Show1) via Generically Exp

-- instance Applicative Exp where pure = V; (<*>) = ap

-- instance Monad Exp where
--   return = V
--   V a      >>= f = f a
--   (x :@ y) >>= f = (x >>= f) :@ (y >>= f)
--   Lam e    >>= f = Lam (e >>>= f)

-- lam :: Eq a => a -> Exp a -> Exp a
-- lam v b = Lam (abstract1 v b)

-- whnf :: Exp a -> Exp a
-- whnf (f :@ a) = case whnf f of
--   Lam b -> whnf (instantiate1 a b)
--   f'    -> f' :@ a
-- whnf e = e

-- test :: IO ()
-- test = do
--   let term = lam 'x' (V 'x') :@ V 'y'
--   print $ term
--   print $ whnf term


data Var b a = B b -- ^ bound variables
             | F a -- ^ free variables
             deriving (Eq, Show, Functor, Foldable, Traversable)
instance Eq2 Var where
  liftEq2 f _ (B a) (B c) = f a c
  liftEq2 _ g (F b) (F d) = g b d
  liftEq2 _ _ _ _ = False
instance Eq b => Eq1 (Var b) where liftEq = liftEq2 (==)
instance Show2 Var where
  liftShowsPrec2 f _ _ _ d (B a) = showsUnaryWith f "B" d a
  liftShowsPrec2 _ _ h _ d (F a) = showsUnaryWith h "F" d a
instance Show b => Show1 (Var b) where
  liftShowsPrec = liftShowsPrec2 showsPrec showList

-- | @'Scope' b f a@ is an @f@ expression with bound variables in @b@,
-- and free variables in @a@
newtype Scope b f a = Scope { unscope :: f (Var b a) }
  deriving (Generic1)
  deriving (Show1, Eq1) via (Generically (Scope b f))
instance (Eq e, Functor m, Eq1 m, Eq a) => Eq (Scope e m a) where (==) = eq1
instance (Show e, Functor m, Show1 m, Show a) => Show (Scope e m a) where showsPrec = showsPrec1

class Bound t where
  -- | Perform substitution
  --
  -- If @t@ is an instance of @MonadTrans@ and you are compiling on GHC >= 7.4, then this
  -- gets the default definition:
  --
  -- @m '>>>=' f = m '>>=' 'lift' '.' f@
  (>>>=) :: Monad f => t f a -> (a -> f c) -> t f c
#if defined(__GLASGOW_HASKELL__)
  default (>>>=) :: (MonadTrans t, Monad f, Monad (t f)) =>
                    t f a -> (a -> f c) -> t f c
  m >>>= f = m >>= lift . f
  {-# INLINE (>>>=) #-}
#endif

instance Bound (Scope b) where
  Scope m >>>= f = Scope $ m >>= \v -> case v of
    B b -> return (B b)
    F a -> liftM F (f a)
  {-# INLINE (>>>=) #-}

instance Functor f => Functor (Scope b f) where
  fmap f (Scope a) = Scope (fmap (fmap f) a)
  {-# INLINE fmap #-}

-- | @'toList'@ is provides a list (with duplicates) of the free variables
instance Foldable f => Foldable (Scope b f) where
  foldMap f (Scope a) = foldMap (foldMap f) a
  {-# INLINE foldMap #-}

instance Traversable f => Traversable (Scope b f) where
  traverse f (Scope a) = Scope <$> traverse (traverse f) a
  {-# INLINE traverse #-}

#if !MIN_VERSION_base(4,8,0)
instance (Functor f, Monad f) => Applicative (Scope b f) where
#else
instance Monad f => Applicative (Scope b f) where
#endif
  pure a = Scope (return (F a))
  {-# INLINE pure #-}
  (<*>) = ap
  {-# INLINE (<*>) #-}

-- | The monad permits substitution on free variables, while preserving
-- bound variables
instance Monad f => Monad (Scope b f) where
#if __GLASGOW_HASKELL__ < 710
  return a = Scope (return (F a))
  {-# INLINE return #-}
#endif
  Scope e >>= f = Scope $ e >>= \v -> case v of
    B b -> return (B b)
    F a -> unscope (f a)
  {-# INLINE (>>=) #-}


-- | @'substitute' a p w@ replaces the free variable @a@ with @p@ in @w@.
--
-- >>> substitute "hello" ["goodnight","Gracie"] ["hello","!!!"]
-- ["goodnight","Gracie","!!!"]
substitute :: (Monad f, Eq a) => a -> f a -> f a -> f a
substitute a p w = w >>= \b -> if a == b then p else return b
{-# INLINE substitute #-}

-- | @'substituteVar' a b w@ replaces a free variable @a@ with another free variable @b@ in @w@.
--
-- >>> substituteVar "Alice" "Bob" ["Alice","Bob","Charlie"]
-- ["Bob","Bob","Charlie"]
substituteVar :: (Functor f, Eq a) => a -> a -> f a -> f a
substituteVar a p = fmap (\b -> if a == b then p else b)
{-# INLINE substituteVar #-}

-- | Capture some free variables in an expression to yield
-- a 'Scope' with bound variables in @b@
--
-- >>> :m + Data.List
-- >>> abstract (`elemIndex` "bar") "barry"
-- Scope [B 0,B 1,B 2,B 2,F 'y']
abstract :: Functor f => (a -> Maybe b) -> f a -> Scope b f a
abstract f e = Scope (fmap k e) where
  k y = case f y of
    Just z  -> B z
    Nothing -> F y
{-# INLINE abstract #-}

-- | Abstract over a single variable
--
-- >>> abstract1 'x' "xyz"
-- Scope [B (),F 'y',F 'z']
abstract1 :: (Functor f, Eq a) => a -> f a -> Scope () f a
abstract1 a = abstract (\b -> if a == b then Just () else Nothing)

-- | Enter a scope, instantiating all bound variables
--
-- >>> :m + Data.List
-- >>> instantiate (\x -> [toEnum (97 + x)]) $ abstract (`elemIndex` "bar") "barry"
-- "abccy"
instantiate :: Monad f => (b -> f a) -> Scope b f a -> f a
instantiate k e = unscope e >>= \v -> case v of
  B b -> k b
  F a -> return a
{-# INLINE instantiate #-}

-- | Enter a 'Scope' that binds one variable, instantiating it
--
-- >>> instantiate1 "x" $ Scope [B (),F 'y',F 'z']
-- "xyz"
instantiate1 :: Monad f => f a -> Scope n f a -> f a
instantiate1 e = instantiate (const e)
{-# INLINE instantiate1 #-}

hoistScope :: (f (Var b a) -> g (Var b a)) -> Scope b f a -> Scope b g a
hoistScope f = Scope . f . unscope
{-# INLINE hoistScope #-}

-- | Perform a change of variables on bound variables.
mapBound :: Functor f => (b -> b') -> Scope b f a -> Scope b' f a
mapBound f (Scope s) = Scope (fmap f' s) where
  f' (B b) = B (f b)
  f' (F a) = F a
{-# INLINE mapBound #-}


-- | Return a list of occurences of the variables bound by this 'Scope'.
bindings :: Foldable f => Scope b f a -> [b]
bindings (Scope s) = foldr f [] s where
  f (B v) vs = v : vs
  f _ vs     = vs
{-# INLINE bindings #-}
