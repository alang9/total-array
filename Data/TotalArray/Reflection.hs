{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.TotalArray.Reflection where

import Prelude
import qualified Prelude as P

import Control.Category
import Data.Proxy
import Data.Reflection
import qualified Data.Vector as VB
import qualified Data.Vector.Generic as G
import qualified Data.Vector.Generic.Mutable as GM

import Data.MySafeInt
import Data.Small.Internal
import Data.TotalArray.Generic (GArray (..))
import qualified Data.TotalArray.Generic as Gen

type Map vec tag a = GArray vec (VecIdx tag) a

newtype VecIdx s = UnsafeVecIdx {unVecIdx :: Int} deriving (Show)

instance (G.Vector vec a, Reifies tag (vec a)) => Bounded (VecIdx tag) where
    minBound = UnsafeVecIdx 0
    maxBound = UnsafeVecIdx $ G.length (reflect (Proxy :: Proxy tag)) - 1

instance (G.Vector vec a, Reifies tag (vec a)) => Small (VecIdx tag) where
    numValues_ _ = toSafe $ G.length (reflect (Proxy :: Proxy tag))
    toIndex_ = \(UnsafeVecIdx x) -> x
    unsafeFromIndex_ = UnsafeVecIdx

tabulate
  :: forall tag vec k a. (Reifies tag (vec k), G.Vector vec k, G.Vector vec a)
  => (k -> a)
  -> Map vec tag a
tabulate f = Array $ G.map f $ reflect (Proxy :: Proxy tag)

tabulateM
  :: forall tag vec k a m. (Reifies tag (vec k), G.Vector vec k, G.Vector vec a, Monad m)
  => (k -> m a)
  -> m (Map vec tag a)
tabulateM f =
  fmap Array $ G.mapM f $ reflect (Proxy :: Proxy tag)


withIndices :: forall vec a r. (G.Vector vec a) => vec a ->
               (forall tag. (Reifies tag (vec a), G.Vector vec a) =>
                Proxy tag -> [VecIdx tag] -> r) -> r
withIndices v f = reify v $
    \p@(Proxy :: Proxy tag) -> f p (take (G.length (reflect p)) [UnsafeVecIdx n |  n <- [0..]])
--    \(Proxy :: Proxy tag) -> f (take (G.length (reflect (Proxy :: Proxy tag))) [UnsafeVecIdx n |  n <- [0..]])

lookup :: forall vec dat tag. (G.Vector vec dat, Reifies tag (vec dat)) => VecIdx tag -> dat
lookup (UnsafeVecIdx n) = reflect (Proxy :: Proxy tag) G.! n

mapWithKey :: forall tag vec k a b. (Reifies tag (vec k), G.Vector vec k, G.Vector vec a, G.Vector vec b) =>
              (k -> a -> b) -> Map vec tag a -> GArray vec k b
mapWithKey f (Array v) = Array $ G.zipWith f (reflect (Proxy :: Proxy tag)) v

mapWithKeyM :: forall tag vec k a b m. (Reifies tag (vec k), G.Vector vec k, G.Vector vec a, G.Vector vec b, Monad m) =>
               (k -> a -> m b) -> Map vec tag a -> m (Map vec tag b)
mapWithKeyM f (Array v) = Array <$> G.zipWithM f (reflect (Proxy :: Proxy tag)) v

intersectionWith :: (Reifies tag (vec k), G.Vector vec a, G.Vector vec b, G.Vector vec c) =>
                    (a -> b -> c) -> Map vec tag a -> Map vec tag b -> Map vec tag c
intersectionWith f (Array v1) (Array v2) = Array $ G.zipWith f v1 v2

intersectionWithKey :: forall tag vec k a b c.
                       (Reifies tag (vec k), G.Vector vec k, G.Vector vec a, G.Vector vec b, G.Vector vec c) =>
                       (k -> a -> b -> c) -> Map vec tag a -> Map vec tag b -> Map vec tag c
intersectionWithKey f (Array v1) (Array v2) = Array $ G.zipWith3 f (reflect (Proxy :: Proxy tag)) v1 v2

reifyWithInjections :: forall tag vec bar foo r. (G.Vector vec bar, G.Vector vec foo, Reifies tag (vec foo)) =>
    Proxy tag -> [foo -> bar] ->
    (forall tag2. Reifies tag2 (vec bar) => [IdxFn tag tag2] -> r) ->
    r
reifyWithInjections p gs f = reify (G.concat $ map (\g -> G.map g (reflect p)) gs) $ \(Proxy :: Proxy tag2) ->
    f (take (length gs) [IdxFn 1 (a * G.length (reflect p)) :: IdxFn tag tag2 | a <- [0..]])


data IdxFn a b = IdxFn {-# UNPACK #-} !Int {-# UNPACK #-} !Int

applyIdxFn :: IdxFn a b -> VecIdx a -> VecIdx b
applyIdxFn (IdxFn a b) (UnsafeVecIdx x) = UnsafeVecIdx $ a * x + b

instance Category IdxFn where
  id = IdxFn 1 0
  IdxFn a b . IdxFn c d = IdxFn (a * c) (a * d + b)
