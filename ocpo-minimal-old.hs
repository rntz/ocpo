{-# LANGUAGE GADTs #-}
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

type S a = [a] -- monotonically increasing infinite streams

data Val a where
  VNat :: S Int -> Val Int
  VFun :: (Val a -> Val b) -> Val (a -> b)

-- Are two types the same?
data Same a b where Refl :: Same a a
same :: Type a -> Type b -> Maybe (Same a b)
same TNat TNat = Just Refl
same (TFun a b) (TFun a' b') | (Just Refl, Just Refl) <- (same a a', same b b') = Just Refl
same _ _ = Nothing

data Binding where Bind :: Var a -> Val a -> Binding
type Env = [Binding]
binding :: Var a -> Env -> Val a
binding (_, xname) [] = error ("unbound variable: " ++ xname)
binding x@(xtp, xname) (Bind (ytp, yname) val : env)
  | xname == yname, Just Refl <- same xtp ytp = val
  | otherwise = binding x env

app :: Val (a -> b) -> Val a -> Val b
app (VFun f) = f

-- the rope trick
delay :: Type a -> Val a -> Val a
delay TNat val = VNat (0 : (case val of VNat s -> s))
delay (TFun a b) val = VFun (\x -> delay b (app val x))

eval :: Env -> Expr a -> Val a
eval env (ENat x) = VNat xs where xs = x : xs
eval env (EVar x) = binding x env
eval env (ELam x body) = VFun (\v -> eval (Bind x v : env) body)
eval env (EApp func arg) = eval env func `app` eval env arg
eval env (EFix x@(xtp, xname) body) = result
  where result = eval (Bind x (delay xtp result) : env) body

-- BUT WHAT DOES IT __DO__???
