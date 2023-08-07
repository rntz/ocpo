{-# LANGUAGE GADTs, TypeFamilies #-}
data Type a where
  TNat :: Type Int
  TFun :: Type a -> Type b -> Type (a -> b)

type Var a = (Type a, String)
data Expr a where
  ENat :: Int -> Expr Int
  EVar :: Var a -> Expr a
  ELam :: Var a -> Expr b -> Expr (a -> b)
  EApp :: Expr (a -> b) -> Expr a -> Expr b
  EFix :: Var a -> Expr a -> Expr a
  EVal :: Val a -> Expr a -- escape hatch for primitives

type Stream a = [a] -- monotonically increasing infinite streams
type family Val a where
  Val Int = Stream Int
  Val (a -> b) = Val a -> Val b

-- Are two types the same?
data Same a b where Refl :: Same a a
same :: Type a -> Type b -> Maybe (Same a b)
same TNat TNat = Just Refl
same (TFun a b) (TFun a' b') | Just Refl <- same a a', Just Refl <- same b b' = Just Refl
same _ _ = Nothing

data Binding where Bind :: Var a -> Val a -> Binding
type Env = [Binding]
binding :: Var a -> Env -> Val a
binding (_, xname) [] = error ("unbound variable: " ++ xname)
binding x@(xtp, xname) (Bind (ytp, yname) val : env)
  | xname == yname, Just Refl <- same xtp ytp = val
  | otherwise = binding x env

eval :: Env -> Expr a -> Val a
eval env (EVal v) = v
eval env (ENat x) = xs where xs = x : xs
eval env (EVar x) = binding x env
eval env (ELam x body) = \v -> eval (Bind x v : env) body
eval env (EApp func arg) = eval env func $ eval env arg
-- The magic trick.
eval env (EFix x@(xtp, xname) body) = result
  where result = eval (Bind x (delay xtp result) : env) body

delay :: Type a -> Val a -> Val a
delay TNat xs = 0 : xs
delay (TFun a b) f = \x -> delay b (f x)
