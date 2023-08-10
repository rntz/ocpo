{-# LANGUAGE GADTs #-}
import Data.List (transpose, intercalate)

type Stream a = [a]     -- monotonically increasing infinite streams
type Nat = Stream Int   -- free ω-cpo on natural numbers under ≤
type Set a = [[a]]      -- finitely generated powerdomain, I think?

data Type a where
  Nat :: Type Nat
  Fun :: Type a -> Type b -> Type (a -> b)
  Set :: Type a -> Type (Set a)

type Var a = (Type a, String)
data Expr a where
  ENat :: Int -> Expr Nat
  EVar :: Var a -> Expr a
  ELam :: (Var a, Expr b) -> Expr (a -> b)
  EApp :: Expr (a -> b) -> Expr a -> Expr b
  ESet :: [Expr a] -> Expr (Set a)
  EFor :: Type b -> Expr (Set a) -> (Var a, Expr b) -> Expr b
  ELub :: Type a -> [Expr a] -> Expr a
  EFix :: Var a -> Expr a -> Expr a
  EVal :: a -> Expr a -- escape hatch for primitives

data Same a b where Refl :: Same a a
same :: Type a -> Type b -> Maybe (Same a b)
same Nat Nat = Just Refl
same (Fun a b) (Fun a' b') | Just Refl <- same a a', Just Refl <- same b b' = Just Refl
same (Set a) (Set a') | Just Refl <- same a a' = Just Refl
same Nat _ = Nothing
same Fun{} _ = Nothing
same Set{} _ = Nothing

data Binding where Bind :: Var a -> a -> Binding
type Env = [Binding]
binding :: Var a -> Env -> a
binding x env = loop x env
  where loop (_, xname) [] = error ("unbound variable " ++ xname ++ ", bound vars: " ++ boundvars)
        loop x@(xtp, xname) (Bind (ytp, yname) val : env)
          | xname == yname, Just Refl <- same xtp ytp = val
          | otherwise = loop x env
        boundvars = intercalate ", " [name | Bind (_, name) _ <- env]

eval :: Env -> Expr a -> a
eval env (EVal v) = v
eval env (ENat x) = xs where xs = x : xs
eval env (EVar x) = binding x env
eval env (ELam (x, body)) = \v -> eval (Bind x v : env) body
eval env (ESet es) = [[eval env e | e <- es]]
eval env (EFor b set (x,body)) = loop (eval env set)
  where loop [] = lub b []
        loop (elems:elemses) = lub b (delay b (loop elemses) : map visit elems)
        visit elem = eval (Bind x elem : env) body
eval env (ELub a es) = lub a [eval env e | e <- es]
eval env (EApp func arg) = eval env func $ eval env arg
-- The magic trick.
eval env (EFix x@(xtp, xname) body) = result
  where result = eval (Bind x (delay xtp result) : env) body

lub :: Type a -> [a] -> a
lub a [x] = x --optimization
lub (Fun a b) fs = \x -> lub b [f x | f <- fs]
lub Nat xss   = map maximum $ transpose xss
lub Set{} xss = map concat  $ transpose xss

delay :: Type a -> a -> a
delay Nat = (0 :)
delay Set{} = ([] :)
delay (Fun a b) = (delay b .)

-- Some useful expr-makers.
delayBy :: Int -> Type a -> Expr a -> Expr a
delayBy n tp = EApp (EVal (loop n))
  where loop 0 x = x
        loop n x = loop (n-1) (delay tp x)

plusOne :: Expr Nat -> Expr Nat
plusOne = EApp (EVal (map (+1)))

-- OK let's try it.
foo :: Expr (Set Nat)
foo = EFix x (EVar x) where x = (Set Nat, "x")

nats :: Expr Nat
nats = EFix x (plusOne (EVar x))
  where x = (Nat, "x")

-- should yield [2,2,2,3,3,3,4,5,6,7,8,9,...]
eset :: Expr (Set Nat)
eset = ESet [ENat 2, delayBy 2 Nat (ENat 3), delayBy 2 Nat nats]

baz :: Expr (Nat)
baz = EFor Nat eset (x, EVar x)
  where x = (Nat, "x")
