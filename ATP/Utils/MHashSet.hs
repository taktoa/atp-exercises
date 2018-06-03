--------------------------------------------------------------------------------

--  Copyright 2018 Remy Goldschmidt
--
--  Licensed under the Apache License, Version 2.0 (the "License");
--  you may not use this file except in compliance with the License.
--  You may obtain a copy of the License at
--
--    http://www.apache.org/licenses/LICENSE-2.0
--
--  Unless required by applicable law or agreed to in writing, software
--  distributed under the License is distributed on an "AS IS" BASIS,
--  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
--  See the License for the specific language governing permissions and
--  limitations under the License.

--------------------------------------------------------------------------------

-- | FIXME: doc
module ATP.Utils.MHashSet
  ( MHashSet
  , new
  , newWithCapacity
  , length
  , null
  , computeOverhead
  , delete
  , member
  , insert
  , mapM_
  , forM_
  , foldM
  , freeze
  , thaw
  , mergeInto
  ) where

--------------------------------------------------------------------------------

import           Prelude                 (Double, Eq, Show, flip, (<$>))

import           Control.Applicative     (pure)
import           Control.Monad           ((>>=))

import           Control.Monad.Primitive (PrimMonad (PrimState))

import           Data.Bool               (Bool)
import           Data.Int                (Int)

import           Data.Maybe              (isJust)

import           Data.Hashable           (Hashable)

import           Data.HashSet            (HashSet)
import qualified Data.HashSet            as HashSet

import           EqSat.Internal.MHashMap (MHashMap)
import qualified EqSat.Internal.MHashMap as MHashMap

import           Flow                    ((.>))

--------------------------------------------------------------------------------

-- * 'MHashSet'

-- | FIXME: doc
newtype MHashSet s k
  = MkMHashSet (MHashMap s k ())
  deriving ()

--------------------------------------------------------------------------------

-- ** Creation

-- | FIXME: doc
new
  :: (PrimMonad m)
  => m (MHashSet (PrimState m) k)
  -- ^ FIXME: doc
new = MkMHashSet <$> MHashMap.new

-- | FIXME: doc
newWithCapacity
  :: (PrimMonad m)
  => Int
  -- ^ FIXME: doc
  -> m (MHashSet (PrimState m) k)
  -- ^ FIXME: doc
newWithCapacity capacity = do
  MkMHashSet <$> MHashMap.newWithCapacity capacity

--------------------------------------------------------------------------------

-- ** Getters

-- | FIXME: doc
length
  :: (PrimMonad m)
  => MHashSet (PrimState m) k
  -- ^ FIXME: doc
  -> m Int
  -- ^ FIXME: doc
length (MkMHashSet mhm) = MHashMap.length mhm

-- | FIXME: doc
null
  :: (PrimMonad m)
  => MHashSet (PrimState m) k
  -- ^ FIXME: doc
  -> m Bool
  -- ^ FIXME: doc
null (MkMHashSet mhm) = MHashMap.null mhm

-- | FIXME: doc
computeOverhead
  :: (PrimMonad m)
  => MHashSet (PrimState m) k
  -- ^ FIXME: doc
  -> m Double
  -- ^ FIXME: doc
computeOverhead (MkMHashSet hm) = MHashMap.computeOverhead hm

--------------------------------------------------------------------------------

-- ** Mutation

-- | FIXME: doc
delete
  :: (Eq k, Hashable k, PrimMonad m)
  => MHashSet (PrimState m) k
  -- ^ FIXME: doc
  -> k
  -- ^ FIXME: doc
  -> m ()
  -- ^ FIXME: doc
delete (MkMHashSet hm) = MHashMap.delete hm

-- | FIXME: doc
member
  :: (Eq k, Hashable k, PrimMonad m)
  => MHashSet (PrimState m) k
  -- ^ FIXME: doc
  -> k
  -- ^ FIXME: doc
  -> m Bool
  -- ^ FIXME: doc
member (MkMHashSet hm) k
  = isJust <$> MHashMap.lookup hm k

-- | FIXME: doc
insert
  :: (Eq k, Hashable k, PrimMonad m)
  => MHashSet (PrimState m) k
  -- ^ FIXME: doc
  -> k
  -- ^ FIXME: doc
  -> m ()
  -- ^ FIXME: doc
insert (MkMHashSet hm) k = MHashMap.insert hm k ()

--------------------------------------------------------------------------------

-- ** Iteration

-- | FIXME: doc
mapM_
  :: (PrimMonad m)
  => (k -> m void)
  -- ^ FIXME: doc
  -> MHashSet (PrimState m) k
  -- ^ FIXME: doc
  -> m ()
  -- ^ FIXME: doc
mapM_ f (MkMHashSet hm) = MHashMap.mapM_ (\k _ -> f k) hm

-- | FIXME: doc
forM_
  :: (PrimMonad m)
  => MHashSet (PrimState m) k
  -- ^ FIXME: doc
  -> (k -> m void)
  -- ^ FIXME: doc
  -> m ()
  -- ^ FIXME: doc
forM_ = flip mapM_

-- | FIXME: doc
foldM
  :: (PrimMonad m)
  => MHashSet (PrimState m) k
  -- ^ FIXME: doc
  -> a
  -- ^ FIXME: doc
  -> (k -> a -> m a)
  -- ^ FIXME: doc
  -> m a
  -- ^ FIXME: doc
foldM (MkMHashSet hm) initial combiner
  = MHashMap.foldM hm initial (\k _ -> combiner k)

--------------------------------------------------------------------------------

-- ** Freezing and thawing

-- | FIXME: doc
freeze
  :: (Eq k, Hashable k, PrimMonad m)
  => MHashSet (PrimState m) k
  -- ^ FIXME: doc
  -> m (HashSet k)
  -- ^ FIXME: doc
freeze hs = foldM hs HashSet.empty (\k -> HashSet.insert k .> pure)

-- | FIXME: doc
thaw
  :: (Eq k, Hashable k, PrimMonad m)
  => HashSet k
  -- ^ FIXME: doc
  -> m (MHashSet (PrimState m) k)
  -- ^ FIXME: doc
thaw hs = do
  result <- newWithCapacity (HashSet.size hs)
  HashSet.foldr (\k x -> x >>= \() -> insert result k) (pure ()) hs
  pure result

--------------------------------------------------------------------------------

-- ** Other useful functions

-- | FIXME: doc
mergeInto
  :: (Eq k, Hashable k, PrimMonad m)
  => MHashSet (PrimState m) k
  -- ^ FIXME: doc
  -> MHashSet (PrimState m) k
  -- ^ FIXME: doc
  -> m ()
  -- ^ FIXME: doc
mergeInto m1 m2 = do
  forM_ m1 (insert m2)

--------------------------------------------------------------------------------
