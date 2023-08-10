module Typeclasses where

import Prelude hiding (head, tail)
import Control.Applicative

data Eventual a = Now a | Later (Eventual a) deriving (Show, Functor)

class Later a where
  later :: a -> a
  never :: a
  never = later never
instance Later (Eventual a) where later = Later
instance Later b => Later (a -> b) where
  later = (later .)
  never _ = never
instance (Later a, Later b) => Later (a,b) where
  later x = (later (fst x), later (snd x))
  never = (never, never)

eventual :: Later b => (a -> b) -> Eventual a -> b
eventual f (Now x) = f x
eventual f (Later x) = later $ eventual f x

-- fromEventual :: Later a => Eventual a -> a
-- fromEventual = eventual id

class (Later a, Semigroup a) => Ocpo a where
  merge :: [a] -> a
  merge [] = never
  merge xs = foldr1 (<>) xs

instance (Ocpo a, Ocpo b) => Ocpo (a, b) where
  merge xys = (merge (map fst xys), merge (map snd xys))

instance (Semigroup a, Semigroup b, Later a, Later b) => Semigroup (Eventual (Either a b)) where
  Later x <> Later y = Later $ x <> y
  x@Later{} <> y@Now{} = (<>) y x -- always put Now first
  Now (Left x) <> y = Now $ Left $ (<>) x $ eventual getLeft y
    where getLeft (Left y) = y
          getLeft Right{} = error "Left/Right conflict"
  Now (Right x) <> y = Now $ Right $ (<>) x $ eventual getRight y
    where getRight (Right y) = y
          getRight Left{} = error "Right/Left conflict"
instance (Ocpo a, Ocpo b) => Ocpo (Eventual (Either a b)) where

-- monotonically increasing infinite streams
-- NB. only Functor/Applicative for _monotone_ functions.
data Stream a = (:.) a (Stream a) deriving (Show, Functor)
instance Applicative Stream where
  pure x = xs where xs = x :. xs
  liftA2 f (x :. xs) (y :. ys) = f x y :. liftA2 f xs ys -- f must be monotone

head (x :. _) = x
tail (_ :. xs) = xs
toList (x :. xs) = x : toList xs

class Pointed a where bottom :: a
instance Pointed a => Later (Stream a) where later = (bottom :.)
instance Semigroup a => Semigroup (Stream a) where (<>) = liftA2 (<>)
instance (Pointed a, Semigroup a) => Ocpo (Stream a) where

-- MaxInt
newtype Max = Max { getMax :: Int } deriving (Num, Eq, Ord)
instance Show Max where show = show . getMax
instance Pointed Max where bottom = 0
instance Semigroup Max where Max x <> Max y = Max (max x y)

-- Okay, let's see if this works.
nats :: Stream Max
nats = fmap (1 +) $ later nats
