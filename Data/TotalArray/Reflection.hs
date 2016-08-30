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
{-# LANGUAGE ViewPatterns #-}

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
import GHC.TypeLits
import Unsafe.Coerce

import Data.Fin
import Data.MySafeInt
import Data.Small.Internal
import Data.TotalArray.Generic (GArray (..))
import qualified Data.TotalArray.Generic as Gen

newtype VecIdx (s :: k) = UnsafeVecIdx {unVecIdx :: Int} deriving (Show)

instance (G.Vector vec a, Reifies tag (vec a)) => Small (VecIdx tag) where
    numValues_ _ = toSafe $ G.length (reflect (Proxy :: Proxy tag))
    toIndex_ = \(UnsafeVecIdx x) -> x
    unsafeFromIndex_ = UnsafeVecIdx

withIndices :: forall vec a r. (G.Vector vec a) => vec a ->
               (forall k (tag :: k). (Reifies tag (vec a), G.Vector vec a) =>
                Proxy tag -> [VecIdx tag] -> r) -> r
withIndices v f = reify v $
    \p@(Proxy :: Proxy tag) -> f (Proxy :: Proxy tag) (take (G.length (reflect p)) [UnsafeVecIdx n |  n <- [0..]])
--    \(Proxy :: Proxy tag) -> f (take (G.length (reflect (Proxy :: Proxy tag))) [UnsafeVecIdx n |  n <- [0..]])

lookup :: forall vec k a. (Small k, G.Vector vec a) => k -> GArray vec k a -> a
lookup n (Array arr) = arr G.! toIndex n

mapWithKey :: forall tag vec k a b. (Reifies tag (vec k), G.Vector vec k, G.Vector vec a, G.Vector vec b) =>
              (k -> a -> b) -> GArray vec tag a -> GArray vec k b
mapWithKey f (Array v) = Array $ G.zipWith f (reflect (Proxy :: Proxy tag)) v

sum :: (Reifies tag (vec k), G.Vector vec a, Num a) => GArray vec tag a -> a
sum (Array v) = G.sum v

mapWithKeyM :: forall tag vec k a b m. (Reifies tag (vec k), G.Vector vec k, G.Vector vec a, G.Vector vec b, Monad m) =>
               (k -> a -> m b) -> GArray vec tag a -> m (GArray vec tag b)
mapWithKeyM f (Array v) = Array <$> G.zipWithM f (reflect (Proxy :: Proxy tag)) v

intersectionWith :: (Reifies tag (vec k), G.Vector vec a, G.Vector vec b, G.Vector vec c) =>
                    (a -> b -> c) -> GArray vec tag a -> GArray vec tag b -> GArray vec tag c
intersectionWith f (Array v1) (Array v2) = Array $ G.zipWith f v1 v2

intersectionWithKey :: forall tag vec k a b c.
                       (Reifies tag (vec k), G.Vector vec k, G.Vector vec a, G.Vector vec b, G.Vector vec c) =>
                       (k -> a -> b -> c) -> GArray vec tag a -> GArray vec tag b -> GArray vec tag c
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

type R n vec a = (Small n, G.Vector vec a)

class ReifiesIndex k (i :: k) where
    treflectIndex :: Tagged i k

newtype MagicIndex k r = MagicIndex (forall i. (ReifiesIndex k i) => Proxy i -> r)

reifyIndex :: forall k r. k -> (forall i. (ReifiesIndex k i) => Proxy i -> r) -> r
reifyIndex i f = unsafeCoerce (MagicIndex f :: MagicIndex k r) i Proxy

reflectIndex :: forall k i. (ReifiesIndex k i) => Proxy i -> k
reflectIndex _ = untag (treflectIndex :: Tagged i k)

class Reifies1 k (f :: k -> Nat)  where
--    reflect1 :: Proxy f -> a
    reflect1 :: forall l. Proxy f -> Proxy l -> ReifiesIndex k l :- ReifiesSize (f l)

newtype Magic1 k r = Magic1 (forall (f :: k -> Nat). (Reifies1 k f) => Proxy f -> r)

reify1 :: forall vec k r. (Small k, G.Vector vec Int) => GArray vec k Int -> (forall (f :: k -> Nat). (Reifies1 k f) => Proxy f -> r) -> r
reify1 i f = unsafeCoerce (Magic1 f :: Magic1 k r) foo Proxy
  where
    foo :: Proxy f -> Proxy l -> ReifiesIndex k l :- ReifiesSize (f l)
    foo _ p = Sub $ reifySize (lookup (reflectIndex p) i) $ \(Proxy :: Proxy pn) -> unsafeCoerce (Dict :: Dict (ReifiesSize pn))

data DArray k (f :: k -> Nat) vec a = DArray (GArray VB.Vector k (vec a))

lookupD :: (ReifiesIndex k i, Small k) => Proxy i -> DArray k f vec a -> GArray vec (Fin (f i)) a
lookupD pi (DArray ga) = Array $ lookup (reflectIndex pi) ga

reifyDependent :: forall k vec b r. (R k vec b, G.Vector vec (vec b), G.Vector vec Int) => GArray vec k (vec b) ->
                  (forall (f :: k -> Nat). Reifies1 k f =>
                      Proxy f ->
                      DArray k f vec b ->
                      r) ->
                  r
reifyDependent a f = reify1 (Gen.map G.length a) $ \p -> f p (DArray $ Gen.convert a)

reifyFinGArray :: forall vec a r. (G.Vector vec a) => vec a -> (forall n. (ReifiesSize n) => GArray vec (Fin n) a -> r) -> r
reifyFinGArray v f = reifySize (G.length v) $ \(Proxy :: Proxy n) -> f (Array v :: GArray vec (Fin n) a)

idxRange :: Small k => Proxy k -> [k]
idxRange p = map fromIndex' $ [0..numValues p - 1]

foo :: [Int]
foo = reifyFinGArray (VB.fromList [1..5] :: VB.Vector Int) $ \(_ :: GArray VB.Vector (Fin n) Int) ->
    let bar :: GArray VB.Vector (Fin n) (VB.Vector Int)
        bar = Gen.tabulate (\(toIndex -> n) -> VB.replicate n n) in
    reifyDependent bar $ \pf@(Proxy :: Proxy f) dBar ->
        reifyIndex (unsafeFromIndex_ 2 :: Fin n) $ \idxP@(Proxy :: Proxy i) -> case reflect1 pf idxP of
            Sub Dict -> map (\i -> lookup i (lookupD idxP dBar)) (idxRange (Proxy :: Proxy (Fin (f i))))
