{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.TotalArray.Reflection where

import Prelude hiding (lookup, sum)
import qualified Prelude as P

import Control.Category
import Data.Constraint
import Data.Kind
import Data.Proxy
import Data.Reflection
import Data.Tagged
import qualified Data.Vector as VB
import qualified Data.Vector.Generic as G
import qualified Data.Vector.Generic.Mutable as GM
import GHC.Exts (Any)
import Unsafe.Coerce

import Data.MySafeInt
import Data.Small.Internal
import Data.TotalArray.Generic (GArray (..))
import qualified Data.TotalArray.Generic as Gen

type Map vec tag a = GArray vec (VecIdx tag) a

newtype VecIdx (s :: k) = UnsafeVecIdx {unVecIdx :: Int} deriving (Show)

instance (G.Vector vec a, Reifies tag (vec a)) => Bounded (VecIdx tag) where
    minBound = UnsafeVecIdx 0
    maxBound = UnsafeVecIdx $ G.length (reflect (Proxy :: Proxy tag)) - 1

instance (G.Vector vec a, Reifies tag (vec a)) => Enum (VecIdx tag) where
    toEnum n
        | n < 0 = error "Enum (VecIdx tag)"
        | n > G.length (reflect (Proxy :: Proxy tag)) - 1 = error "Enum (VecIdx tag)"
        | otherwise = UnsafeVecIdx n
    fromEnum = unVecIdx

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
               (forall k (tag :: k). (Reifies tag (vec a), G.Vector vec a) =>
                Proxy tag -> [VecIdx tag] -> r) -> r
withIndices v f = reify v $
    \p@(Proxy :: Proxy tag) -> f (Proxy :: Proxy tag) (take (G.length (reflect p)) [UnsafeVecIdx n |  n <- [0..]])
--    \(Proxy :: Proxy tag) -> f (take (G.length (reflect (Proxy :: Proxy tag))) [UnsafeVecIdx n |  n <- [0..]])

lookup :: forall vec dat tag. (G.Vector vec dat, Reifies tag (vec dat)) => VecIdx tag -> dat
lookup (UnsafeVecIdx n) = reflect (Proxy :: Proxy tag) G.! n

lookupMap :: forall vec dat tag a. (G.Vector vec dat, Reifies tag (vec dat), G.Vector vec a) => VecIdx tag -> Map vec tag a -> a
lookupMap (UnsafeVecIdx n) (Array arr) = arr G.! n

mapWithKey :: forall tag vec k a b. (Reifies tag (vec k), G.Vector vec k, G.Vector vec a, G.Vector vec b) =>
              (k -> a -> b) -> Map vec tag a -> GArray vec k b
mapWithKey f (Array v) = Array $ G.zipWith f (reflect (Proxy :: Proxy tag)) v

sum :: (Reifies tag (vec k), G.Vector vec a, Num a) => Map vec tag a -> a
sum (Array v) = G.sum v

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
    (forall k1 (tag2 :: k1). Reifies tag2 (vec bar) => [IdxFn tag tag2] -> r) ->
    r
reifyWithInjections p gs f = reify (G.concat $ map (\g -> G.map g (reflect p)) gs) $ \(Proxy :: Proxy tag2) ->
    f (take (length gs) [IdxFn 1 (a * G.length (reflect p)) :: IdxFn tag tag2 | a <- [0..]])


data IdxFn a b = IdxFn {-# UNPACK #-} !Int {-# UNPACK #-} !Int

applyIdxFn :: IdxFn a b -> VecIdx a -> VecIdx b
applyIdxFn (IdxFn a b) (UnsafeVecIdx x) = UnsafeVecIdx $ a * x + b

instance Category IdxFn where
  id = IdxFn 1 0
  IdxFn a b . IdxFn c d = IdxFn (a * c) (a * d + b)

type R tag vec a = (Reifies tag (vec a), G.Vector vec a)


class ReifiesIndex k (i :: k) where
    treflectIndex :: Tagged i k

newtype MagicIndex k r = MagicIndex (forall i. (ReifiesIndex k i) => Proxy i -> r)

reifyIndex :: forall k r. k -> (forall i. (ReifiesIndex k i) => Proxy i -> r) -> r
reifyIndex i f = unsafeCoerce (MagicIndex f :: MagicIndex k r) i Proxy

reflectIndex :: forall k i. (ReifiesIndex k i) => Proxy i -> k
reflectIndex _ = untag (treflectIndex :: Tagged i k)

class Reifies1 k (f :: VecIdx k -> *) a | k f -> a where
    reflect1 :: Proxy f -> a

newtype Magic1 k a r = Magic1 (forall (f :: VecIdx k -> *). (Reifies1 k f a) => Proxy f -> r)

reify1 :: forall k a r. a -> (forall (f :: VecIdx k -> *). (Reifies1 k f a) => Proxy f -> r) -> r
reify1 i f = unsafeCoerce (Magic1 f :: Magic1 k a r) i Proxy

reifyDependent :: forall k vec b r a. (R k vec a, G.Vector vec b) => Map vec k b ->
                  (forall (f :: VecIdx k -> *). Reifies1 k f (Map vec k b) => Proxy f -> (forall (l :: VecIdx k). ReifiesIndex (VecIdx k) l => Proxy l -> Dict (Reifies (f l) b)) -> r) ->
                  r
reifyDependent a f = reify1 a $ \p -> f p (\pl -> reify (lookupMap (reflectIndex pl) a) (\(Proxy :: Proxy pp) -> unsafeCoerce (Dict :: Dict (Reifies pp b))))

foo :: [Int]
foo = reify (VB.fromList [1..5] :: VB.Vector Int) $ \(Proxy :: Proxy matsTag) ->
    let bar :: Map VB.Vector matsTag (VB.Vector Int)
        bar = tabulate (\n -> VB.replicate n n) in
    reifyDependent bar $ \(Proxy :: Proxy f) baz ->
        reifyIndex (UnsafeVecIdx 2 :: VecIdx matsTag) $ \idxP@(Proxy :: Proxy i) -> case baz idxP of
            Dict -> map lookup [minBound .. (maxBound :: VecIdx (f i))]
