{-# LANGUAGE PolymorphicComponents
            ,MultiParamTypeClasses
            ,FunctionalDependencies
            ,FlexibleInstances
 #-}

{-|

The main SAT solver monad.  Embeds `ST'.  See type `SSTErrMonad', which stands
for ''State ST Error Monad''.

Most of the work done is in the form of `SSTErrMonad' actions. -}
module DPLL.Monad where

import Control.Monad.Error hiding ((>=>), forM_)
import Control.Monad.ST.Strict
import Control.Monad.State.Lazy hiding ((>=>), forM_)
import Control.Monad.MonadST


instance MonadST s (SSTErrMonad e st s) where
    liftST = dpllST

-- | Perform an @ST@ action in the DPLL monad.
dpllST :: ST s a -> SSTErrMonad e st s a
{-# INLINE dpllST #-}
dpllST st = SSTErrMonad (\k s -> st >>= \x -> k x s)

-- | @runSSTErrMonad m s@ executes a `SSTErrMonad' action with initial state @s@
-- until an error occurs or a result is returned.
runSSTErrMonad :: (Error e) => SSTErrMonad e st s a -> (st -> ST s (Either e a, st))
runSSTErrMonad m = unSSTErrMonad m (\x s -> return (return x, s))

evalSSTErrMonad :: (Error e) => SSTErrMonad e st s a -> st -> ST s (Either e a)
evalSSTErrMonad m s = do (result, _) <- runSSTErrMonad m s
                         return result

-- | @SSTErrMonad e st s a@: the error type @e@, state type @st@, @ST@ thread
-- @s@ and result type @a@.
--
-- This is a monad embedding @ST@ and supporting error handling and state
-- threading.  It uses CPS to avoid checking `Left' and `Right' for every
-- `>>='; instead only checks on `catchError'. Idea adapted from
-- <http://haskell.org/haskellwiki/Performance/Monads>.
newtype SSTErrMonad e st s a =
    SSTErrMonad { unSSTErrMonad :: forall r. (a -> (st -> ST s (Either e r, st)))
                              -> (st -> ST s (Either e r, st)) }

instance Monad (SSTErrMonad e st s) where
    return x = SSTErrMonad ($ x)
    m >>= f  = bindSSTErrMonad m f

bindSSTErrMonad :: SSTErrMonad e st s a -> (a -> SSTErrMonad e st s b) -> SSTErrMonad e st s b
{-# INLINE bindSSTErrMonad #-}
bindSSTErrMonad m f = SSTErrMonad (\k -> unSSTErrMonad m (\a -> unSSTErrMonad (f a) k))

instance MonadState st (SSTErrMonad e st s) where
    get = SSTErrMonad (\k s -> k s s)
    put s' = SSTErrMonad (\k _ -> k () s')

instance (Error e) => MonadError e (SSTErrMonad e st s) where
    throwError err =            -- throw away continuation
        SSTErrMonad (\_ s -> return (Left err, s))
    catchError action handler = SSTErrMonad
        (\k s -> do (x, s') <- runSSTErrMonad action s
                    case x of
                      Left error -> unSSTErrMonad (handler error) k s'
                      Right result -> k result s')
