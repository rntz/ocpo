{-# LANGUAGE GADTs #-}
type Stream a = [a]   -- monotonically increasing infinite streams
type Nat = Stream Int -- free ω-cpo on natural numbers under ≤

data Type a where
  Nat :: Type Nat
  Fun :: Type a -> Type b -> Type (a -> b)

type Var a = (Type a, String)
data Expr a where
  ENat :: Int -> Expr Nat
  EVar :: Var a -> Expr a
  ELam :: Var a -> Expr b -> Expr (a -> b)
  EApp :: Expr (a -> b) -> Expr a -> Expr b
  EFix :: Var a -> Expr a -> Expr a
  EVal :: a -> Expr a -- escape hatch for primitives

-- Are two types the same?
data Same a b where Refl :: Same a a
same :: Type a -> Type b -> Maybe (Same a b)
same Nat Nat = Just Refl
same (Fun a b) (Fun a' b') | Just Refl <- same a a', Just Refl <- same b b' = Just Refl
same _ _ = Nothing

data Binding where Bind :: Var a -> a -> Binding
type Env = [Binding]
binding :: Var a -> Env -> a
binding (_, xname) [] = error ("unbound variable: " ++ xname)
binding x@(xtp, xname) (Bind (ytp, yname) val : env)
  | xname == yname, Just Refl <- same xtp ytp = val
  | otherwise = binding x env

eval :: Env -> Expr a -> a
eval env (EVal v) = v
eval env (ENat x) = xs where xs = x : xs
eval env (EVar x) = binding x env
eval env (ELam x body) = \v -> eval (Bind x v : env) body
eval env (EApp func arg) = eval env func $ eval env arg
-- The magic trick.
eval env (EFix x@(xtp, xname) body) = result
  where result = eval (Bind x (delay xtp result) : env) body

delay :: Type a -> a -> a
delay Nat = (0 :)
delay (Fun a b) = (delay b .)
