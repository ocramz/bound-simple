module Bound.Simple where

import Control.Monad.Trans.Except (ExceptT(..), mapExcept)


-- | Left : bound vars
-- right : free vars
newtype Scope b f a = Scope { unscope :: ExceptT b f a }
