{-# LANGUAGE GADTs, TypeFamilies, ScopedTypeVariables #-}
data Type a where
  Nat :: Type Int
  Sum :: Type a -> Type b -> Type (Either a b)
  Pair :: Type a -> Type b -> Type (a, b)
  Fun :: Type a -> Type b -> Type (a -> b)

type Semilattice a = Type a -- for now all types are semilattices

-- Expressions.
type Var a = (Type a, String)
data Expr a where
  EVal :: Val a -> Expr a -- escape hatch for primitives
  ENat :: Int -> Expr Int
  -- variables & functions
  EVar :: Var a -> Expr a
  ELam :: Var a -> Expr b -> Expr (a -> b)
  EApp :: Expr (a -> b) -> Expr a -> Expr b
  -- pairs
  EPair :: Expr a -> Expr b -> Expr (a,b)
  EPi1 :: Expr (a,b) -> Expr a
  EPi2 :: Expr (a,b) -> Expr b
  -- sums
  EInj :: Either (Expr a) (Expr b) -> Expr (Either a b)
  ECase :: Type c -> Expr (Either a b) -> (Var a, Expr c) -> (Var b, Expr c) -> Expr c
  -- semilattices & fixed points
  ELub :: Semilattice a -> [Expr a] -> Expr a
  EFix :: Var a -> Expr a -> Expr a

-- Values
type Stream a = [a] -- monotonically increasing infinite streams
data Eventual a = Now a | Later (Eventual a) deriving (Show, Functor)

type family Val a where
  Val Int = Stream Int
  Val (Either a b) = Eventual (Either (Val a) (Val b))
  Val (a, b) = (Val a, Val b)
  Val (a -> b) = Val a -> Val b

-- Are two types the same?
data Same a b where Refl :: Same a a
same :: Type a -> Type b -> Maybe (Same a b)
same Nat Nat = Just Refl
same (Fun a b) (Fun a' b') | Just Refl <- same a a', Just Refl <- same b b' = Just Refl
same (Sum a b) (Sum a' b') | Just Refl <- same a a', Just Refl <- same b b' = Just Refl
same (Pair a b) (Pair a' b') | Just Refl <- same a a', Just Refl <- same b b' = Just Refl
same Nat _ = Nothing
same Fun{} _ = Nothing
same Sum{} _ = Nothing
same Pair{} _ = Nothing

-- Environments bind vars to vals
data Binding where Bind :: Var a -> Val a -> Binding
type Env = [Binding]
binding :: Var a -> Env -> Val a
binding (xtp, xname) ys = search ys
  where search [] = error ("unbound variable: " ++ xname)
        search (Bind (ytp, yname) val : ys)
          | xname == yname, Just Refl <- same xtp ytp = val
          | xname == yname = error ("variable shadowed with different type: " ++ xname)
          | otherwise = search ys

eval :: Env -> Expr a -> Val a
eval env (EVal v) = v
eval env (ENat x) = xs where xs = x : xs
eval env (EVar x) = binding x env
eval env (ELam x body) = \v -> eval (Bind x v : env) body
eval env (EApp func arg) = eval env func $ eval env arg
-- pairs
eval env (EPair e1 e2) = (eval env e1, eval env e2)
eval env (EPi1 e) = fst $ eval env e
eval env (EPi2 e) = snd $ eval env e
-- sums
eval env (EInj (Left  e)) = Now $ Left  $ eval env e
eval env (EInj (Right e)) = Now $ Right $ eval env e
eval env (ECase ctp subj (x,left) (y,right)) = examine $ eval env subj
  where examine (Now (Left v))  = eval (Bind x v : env) left
        examine (Now (Right v)) = eval (Bind y v : env) right
        examine (Later q)       = delay ctp $ examine q
-- lub & fix
eval env (ELub tp es) = lub tp $ map (eval env) es
eval env (EFix x@(xtp, xname) body) = result
  where result = eval (Bind x (delay xtp result) : env) body

-- The rope trick.
-- NB. DO NOT FORCE THUNKS! NO PATTERN MATCHING!
delay :: Type a -> Val a -> Val a
delay Nat        = (0 :)
delay (Pair a b) = \x -> (delay a (fst x), delay b (snd x))
delay (Fun a b)  = (delay b .)
delay Sum{}      = Later

-- Eventual is, like, the initial Delay-algebra or something?
-- a monad-but-stronger-elimination rule, like Set elimination in Datafun
eventually :: Type b -> (a -> Val b) -> Eventual a -> Val b
eventually tp f (Now x)   = f x
eventually tp f (Later x) = delay tp (eventually tp f x)

-- Type-indexed operations.
lub :: Semilattice a -> [Val a] -> Val a
lub Nat xss = maximum (0 : map head xss) : lub Nat (map tail xss)
lub (Fun a b) fs = \x -> lub b [f x | f <- fs]
lub (Pair a b) xys = (lub a (map fst xys), lub b (map snd xys))
lub (Sum a b) xs = foldr combine infty xs
  where infty = Later infty
        combine (Later x) (Later y) = Later $ combine x y
        combine x@Later{} y@Now{} = combine y x -- always put Now first
        combine (Now (Left x)) y = Now . Left $ lub a [x, eventually a fromLeft y]
          where fromLeft  (Left  q) = q
                fromLeft  (Right _) = error "Left/Right conflict"
        combine (Now (Right x)) y = Now . Right $ lub b [x, eventually b fromRight y]
          where fromRight (Right q) = q
                fromRight (Left  _) = error "Right/Left conflict"


-- BUT WHAT DOES IT __DO__???

ex :: Int -> Expr Int -> [Int]
ex n e = take n $ eval [] e

-- TODO:
-- f left = {0} union {x+1 for x in f right}
-- f rght = {x+1 for x in f left}

-- defining the bottom stream recursively works
simple :: Expr Int
simple = EFix x (EVar x) where x = (Nat, "x")

-- defining the bottom function recursively works, remarkably!
dumb = EApp (EFix f (EVar f)) (ENat 0)
  where f = (Fun Nat Nat, "f")

plusOne :: Expr (Int -> Int)
plusOne = EVal (map (+1))

-- Stream of ever-increasing naturals: x = x + 1. Works.
omega :: Expr Int
omega = EFix x (EApp plusOne (EVar x)) where x = (Nat, "x")

-- A step on the way: f x = 1 + f x
omega2 :: Expr Int
omega2 = EApp (EFix f $ ELam x $ EApp plusOne $ EApp (EVar f) (EVar x))
              (ENat 0)
  where f = (Fun Nat Nat, "f")
        x = (Nat, "x")

at :: Int -> Expr (Int -> a) -> Expr a
at n = flip EApp (ENat n)

-- Tests for ELub (TODO: at sum type)
-- f = (\x -> f (x + 1)) join (\x -> 4)
funjoin :: Expr Int
funjoin = at 3 $ EFix f $ ELub ftp [ ELam x (EApp ef (EApp plusOne ex))
                                   , ELam x (ENat 4) ]
  where ftp = Fun Nat Nat
        f = (ftp, "f"); x = (Nat, "x")
        ef = EVar f; ex = EVar x

sumjoin :: Expr Int
sumjoin = undefined

-- TODO: tests for pair types
-- TODO: tests for sum types
