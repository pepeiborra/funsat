{-# LANGUAGE   MultiParamTypeClasses
             , FlexibleInstances #-}

-- | A max heap implemented with 2-3 finger trees.  Supports two important
-- operations: `increaseKey' and `decreaseKey'.
module Data.Heap.Finger
#ifndef TESTING
    ( Info(..)
    , Heap
    , empty
    , insert
    , insertKV
    , extractMax
    , increaseKey
    , merge )
#endif
    where

import Prelude hiding ( foldr, elem )
import Data.Foldable ( foldr, elem, foldl' )
import Data.Monoid
import Data.FingerTree hiding ( empty, null )
import qualified Data.FingerTree as FT

data Prio a = MInfty | Prio a
              deriving (Eq, Ord, Show)

instance (Ord k) => Monoid (Prio k) where
    mempty             = MInfty
    MInfty `mappend` p = p
    p `mappend` MInfty = p
    Prio m `mappend` Prio n = Prio (m `max` n)

-- | Info kept for each node in the tree.
data Info k a = Info
    { key    :: k
    , datum  :: a }
                deriving (Eq, Ord, Show)


-- | Heap storing values of type @a@ and keys of type @k@.  The key type must
-- be ordered.
newtype Heap k a = Heap (FingerTree (Prio k) (Info k a))
    deriving Show

-- | /O(n)/ Map a monotonic function over the heap.
fmapMonotonic :: (Ord k, Ord k') =>
                 (Info k a -> Info k' a')
              -> Heap k a
              -> Heap k' a'
fmapMonotonic f (Heap t) = Heap $ fmapOrd' f t
    where fmapOrd' f t = case viewl t of
                           EmptyL -> FT.empty
                           x :< rs -> f x <| fmapOrd' f rs

fmap' f (Heap t) = Heap $ FT.fmap' f t

instance (Ord k) => Measured (Prio k) (Info k a) where
    measure = Prio . key

empty :: (Ord k) => Heap k a
empty = Heap FT.empty

null :: (Ord k) => Heap k a -> Bool
null (Heap t) = FT.null t

insert :: (Ord k) => Info k a -> Heap k a -> Heap k a
insert info (Heap t) = Heap (info <| t)

insertKV :: (Ord k) => k -> a -> Heap k a -> Heap k a
insertKV k v = insert (Info k v)

-- | Extract the value whose key is maximum.  If more than one key has maximum
-- value, an arbitrary one is chosen.
--
-- Precondition: The heap is non-empty.
extractMax :: (Ord k) => Heap k a -> (Info k a, Heap k a)
extractMax (Heap q) = (i, Heap (l >< r))
    where i :< r  = viewl r'
          (l, r') = split (measure q <=) q

-- | If ''old'' key does not exist in the heap, it is inserted.
increaseKey :: (Ord k, Eq a) =>
            Info k a              -- ^ old
            -> k                  -- ^ new
            -> Heap k a
            -> Heap k a
increaseKey oldInfo newKey (Heap t) = Heap (l >< eqs' >< r')
    where (l, r)    = split (>= measure oldInfo) t
          (eqs, r') = split (> measure oldInfo) r
          eqs' = foldr (\i t' -> if i == oldInfo then newInfo <| t' else i <| t')
                 FT.empty eqs
          newInfo = oldInfo{ key = newKey }

member :: (Ord k, Eq a) => Info k a -> Heap k a -> Bool
member x (Heap t) = x `elem` t

merge :: (Ord k) => Heap k a -> Heap k a -> Heap k a
merge (Heap xs) (Heap ys) = Heap (merge' xs ys)
    where merge' as bs = case viewl bs of
                           EmptyL -> as
                           a :< bs' -> l >< (a <| merge' bs' r)
                               where (l, r) = split (> measure a) as

fromList :: (Ord k) => [Info k a] -> Heap k a
fromList = foldl' (flip insert) empty
