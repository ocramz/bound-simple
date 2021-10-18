# bound-simple

A lightweight implementation of 'bound'. Provides much of the functionality of Bound.Scope.Simple, without the large dependency footprint.

## Example 

The function `whnf` beta-reduces a term of the untyped lambda calculus.

In the code below, we first declare a type `Exp` for terms, using the `Scope` type within the constructor for a lambda abstraction. To this we add a few instances necessary for showing and traversing the terms. The Monad instance takes care of variable substitution.
After that, abstraction and application are implemented in terms of abstract1 and instantiate1.
The `test` function declares a term `(\x . x) y` , then prints it and its reduced form.



```haskell
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}

import Control.Monad (ap)
import Bound.Simple (Scope, Bound(..), abstract1, instantiate1)
import Data.Functor.Classes.Generic (Generically(..))

import GHC.Generics (Generic1)

infixl 9 :
data Exp a = V a | Exp a : Exp a | Lam (Scope () Exp a)
  deriving (Show, Functor, Foldable, Traversable, Generic1)
  deriving (Show1) via Generically Exp

instance Applicative Exp where pure = V; k <*> m = ap k m

instance Monad Exp where
  return = V
  V a      >>= f = f a
  (x :@ y) >>= f = (x >>= f) :@ (y >>= f)
  Lam e    >>= f = Lam (e >>>= f)

lam :: Eq a => a -> Exp a -> Exp a
lam v b = Lam (abstract1 v b)

whnf :: Exp a -> Exp a
whnf (e1 :@ e2) = case whnf e1 of
  Lam b -> whnf (instantiate1 e2 b)
  f'    -> f' :@ e2
whnf e = e

test :: IO ()
test = do
  let term = lam x (V x) :@ V y
  print term         -- Lam (Scope (V (B ()))) :@ V y
  print $ whnf term  -- V y
```
