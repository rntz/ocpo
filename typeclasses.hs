module Typeclasses where

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

class Merge2 a where merge2 :: a -> a -> a
class (Later a, Merge2 a) => Ocpo a where
  merge  :: [a] -> a
  merge = foldr merge2 never

instance (Merge2 a, Merge2 b) => Merge2 (a, b) where merge2 (a,x) (b,y) = (merge2 a b, merge2 x y)
instance (Ocpo a, Ocpo b) => Ocpo (a, b) where merge xys = (merge (map fst xys), merge (map snd xys))

instance (Merge2 a, Merge2 b, Later a, Later b) => Merge2 (Eventual (Either a b)) where
  merge2 (Later x) (Later y) = Later $ merge2 x y
  merge2 x@Later{} y@Now{} = merge2 y x -- always put Now first
  merge2 (Now (Left x)) y = Now $ Left $ merge2 x $ eventual getLeft y
    where getLeft (Left y) = y
          getLeft Right{} = error "Left/Right conflict"
  merge2 (Now (Right x)) y = Now $ Right $ merge2 x $ eventual getRight y
    where getRight (Right y) = y
          getRight Left{} = error "Right/Left conflict"

instance (Ocpo a, Ocpo b) => Ocpo (Eventual (Either a b)) where

-- monotonically increasing infinite streams
-- NB. only a Functor for _monotone_ functions.
data Stream a = Cons a (Stream a) deriving (Show, Functor)
instance Applicative Stream where
  pure x = xs where xs = Cons x xs
  -- NB. assumes the stream of functions is monotonically increasing *and* that they are
  -- all monotone!
  Cons f fs <*> Cons x xs = Cons (f x) (fs <*> xs)

class Pointed a where bottom :: a
instance Pointed a => Later (Stream a) where later = Cons bottom
instance Merge2 a => Merge2 (Stream a) where
  merge2 (Cons x xs) (Cons y ys) = Cons (merge2 x y) (merge2 xs ys)
