{-# LANGUAGE GADTs, TypeFamilies #-}
import Data.Maybe (catMaybes)

-- TODO: pair & sum types
data Type a where
  TNat :: Type Int
  TSum :: Type a -> Type b -> Type (Either a b)
  TFun :: Type a -> Type b -> Type (a -> b)

type Semilattice a = Type a -- for now all types are semilattices

-- Expressions. TODO: semilattice join.
type Var a = (Type a, String)
data Expr a where
  EVal :: Val a -> Expr a -- escape hatch for primitives
  ENat :: Int -> Expr Int
  EVar :: Var a -> Expr a
  ELam :: Var a -> Expr b -> Expr (a -> b)
  EApp :: Expr (a -> b) -> Expr a -> Expr b
  ELub :: Semilattice a -> [Expr a] -> Expr a
  EFix :: Var a -> Expr a -> Expr a

-- Values
type Stream a = [a] -- monotonically increasing infinite streams
type family Val a where
  Val Int = Stream Int
  Val (Either a b) = Maybe (Either (Val a) (Val b))
  Val (a -> b) = Val a -> Val b

-- Are two types the same?
data Same a b where Refl :: Same a a
same :: Type a -> Type b -> Maybe (Same a b)
same TNat TNat = Just Refl
same (TFun a b) (TFun a' b') | Just Refl <- same a a', Just Refl <- same b b' = Just Refl
same (TSum a b) (TSum a' b') | Just Refl <- same a a', Just Refl <- same b b' = Just Refl
same TNat _ = Nothing
same TFun{} _ = Nothing
same TSum{} _ = Nothing

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
eval env (ELub tp es) = lub tp $ map (eval env) es
-- The magic trick.
eval env (EFix x@(xtp, xname) body) = result
  where result = eval (Bind x (delay xtp result) : env) body

-- Type-indexed operations.
lub :: Semilattice a -> [Val a] -> Val a
lub TNat xss = maximum (0 : map head xss) : lub TNat (map tail xss)
lub (TFun a b) fs = \x -> lub b [f x | f <- fs]
lub (TSum a b) xs =
  case catMaybes xs of
    [] -> Nothing
    (Left x : xs) -> undefined
    (Right x : xs) -> undefined

delay :: Type a -> Val a -> Val a
delay TNat xs = 0 : xs
delay (TFun a b) f = \x -> delay b (f x)
delay (TSum a b) _ = Nothing -- UH OH THIS SEEMS WRONG

-- BUT WHAT DOES IT __DO__???

ex :: Int -> Env -> Expr Int -> [Int]
ex n env e = take n $ eval env e

-- TODO:
-- f left = {0} union {x+1 for x in f right}
-- f rght = {x+1 for x in f left}

-- defining the bottom stream recursively works
simple :: Expr Int
simple = EFix x (EVar x) where x = (TNat, "x")

-- defining the bottom function recursively works, remarkably!
dumb = EApp (EFix f (EVar f)) (ENat 0)
  where f = (TFun TNat TNat, "f")

plusOne :: Expr (Int -> Int)
plusOne = EVal (map (+1))

-- Stream of ever-increasing naturals: x = x + 1. Works.
omega :: Expr Int
omega = EFix x (EApp plusOne (EVar x)) where x = (TNat, "x")

-- A step on the way: f x = 1 + f x
omega2 :: Expr Int
omega2 = EApp (EFix f $ ELam x $ EApp plusOne $ EApp (EVar f) (EVar x))
              (ENat 0)
  where f = (TFun TNat TNat, "f")
        x = (TNat, "x")

-- TODO: tests for ELub (esp. at function type)
