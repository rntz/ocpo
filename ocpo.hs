{-# LANGUAGE GADTs #-}
import Data.List (transpose)

-- Eventual is Capretta's delay monad; see eg "Partiality, Revisited" (Altenkirch et al)
-- https://arxiv.org/abs/1610.09254
-- but we don't seem to use the monad structure - weird, huh? dunno what to make of that.
data Eventual a = Now a | Later (Eventual a) deriving (Show, Functor)
never :: Eventual a
never = Later never

type Nat = [Int]                     -- monotonically increasing infinite streams
type Boole = Eventual ()             -- a boolean is false until it's true
-- Set is a finitely generated powerdomain, represented by [elems_0, elems_1, elems_2...]
-- where elems_t is the elems discovered "at time t".
type Set a = [[a]]
type Sum a b = Eventual (Either a b) -- Eventual adds a bottom to sum types

data Type a where
  Nat  :: Type Nat
  Sum  :: Type a -> Type b -> Type (Sum a b)
  Pair :: Type a -> Type b -> Type (a, b)
  Set  :: Type a -> Type (Set a)
  Fun  :: Type a -> Type b -> Type (a -> b)
  Boole :: Type Boole

type Semilattice a = Type a -- for now all types are semilattices

-- Expressions.
type Var a = (Type a, String)
data Expr a where
  EVal :: a -> Expr a -- escape hatch for primitives
  ENat :: Int -> Expr Nat
  -- variables & functions
  EVar :: Var a -> Expr a
  ELam :: Var a -> Expr b -> Expr (a -> b)
  EApp :: Expr (a -> b) -> Expr a -> Expr b
  -- pairs
  EPair :: Expr a -> Expr b -> Expr (a,b)
  EPi1 :: Expr (a,b) -> Expr a
  EPi2 :: Expr (a,b) -> Expr b
  -- sums
  EInj :: Either (Expr a) (Expr b) -> Expr (Sum a b)
  ECase :: Type c -> Expr (Sum a b) -> (Var a, Expr c) -> (Var b, Expr c) -> Expr c
  -- booleans. true is (EAnd []); false is (ELub Boole []).
  EAnd :: [Expr Boole] -> Expr Boole
  -- when false _ = bottom; when true x = x
  EWhen :: Type a -> Expr Boole -> Expr a -> Expr a
  -- sets
  ESet :: [Expr a] -> Expr (Set a)
  EFor :: Type b -> Expr (Set a) -> (Var a, Expr b) -> Expr b
  -- semilattices & fixed points
  ELub :: Semilattice a -> [Expr a] -> Expr a
  EFix :: Var a -> Expr a -> Expr a

-- Are two types the same?
data Same a b where Refl :: Same a a
same :: Type a -> Type b -> Maybe (Same a b)
same Nat Nat = Just Refl
same Boole Boole = Just Refl
same (Fun a b) (Fun a' b') | Just Refl <- same a a', Just Refl <- same b b' = Just Refl
same (Sum a b) (Sum a' b') | Just Refl <- same a a', Just Refl <- same b b' = Just Refl
same (Pair a b) (Pair a' b') | Just Refl <- same a a', Just Refl <- same b b' = Just Refl
same (Set a) (Set a') | Just Refl <- same a a' = Just Refl
same Nat _ = Nothing
same Boole _ = Nothing
same Fun{} _ = Nothing
same Sum{} _ = Nothing
same Pair{} _ = Nothing
same Set{} _ = Nothing

-- Environments bind vars to vals
data Binding where Bind :: Var a -> a -> Binding
type Env = [Binding]
binding :: Var a -> Env -> a
binding (xtp, xname) ys = search ys
  where search [] = error ("unbound variable: " ++ xname)
        search (Bind (ytp, yname) val : ys)
          | xname == yname, Just Refl <- same xtp ytp = val
          | xname == yname = error ("variable shadowed with different type: " ++ xname)
          | otherwise = search ys

eval :: Env -> Expr a -> a
eval env (EVal v) = v
eval env (ENat x) = xs where xs = x : xs
-- variables & functions
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
-- booleans
eval env (EAnd es) = loop [eval env e | e <- es]
  where loop xs = doneYet [x | Later x <- xs]
        doneYet [] = Now ()
        doneYet l = Later $ loop l
eval env (EWhen b e body) = eventually b (\() -> eval env body) (eval env e)
-- sets
eval env (ESet es) = [[eval env e | e <- es]]
eval env (EFor b set (x,body)) = loop (eval env set)
  where loop [] = lub b []
        loop (elems:elemses) = lub b (delay b (loop elemses) : map visit elems)
        visit elem = eval (Bind x elem : env) body
-- lub & fix
eval env (ELub tp es) = lub tp $ map (eval env) es
eval env (EFix x@(xtp, xname) body) = result
  where result = eval (Bind x (delay xtp result) : env) body


-- TYPE-INDEXED OPERATIONS --

-- The rope trick.
-- NB. DO NOT FORCE THUNKS! NO PATTERN MATCHING!
delay :: Type a -> a -> a
delay Nat        = (0 :)
delay Boole      = Later
delay Set{}      = ([] :)
delay (Pair a b) = \x -> (delay a (fst x), delay b (snd x))
delay Sum{}      = Later
delay (Fun a b)  = (delay b .)

-- Eventual is, like, the initial Delay-algebra or something?
-- a monad-but-stronger-elimination rule, like Set elimination in Datafun
eventually :: Type b -> (a -> b) -> Eventual a -> b
eventually tp f (Now x)   = f x
eventually tp f (Later x) = delay tp (eventually tp f x)

lub :: Semilattice a -> [a] -> a
lub Nat xss   = map (maximum . (0:)) $ transpose xss
lub Boole xs = loop [] xs
  where loop acc (Now () : _) = Now () -- early exit
        loop acc (Later x : xs) = loop (x : acc) xs
        loop [] [] = never
        loop acc [] = Later (lub Boole acc)
lub Set{} xss = map concat $ transpose xss
lub (Fun a b) fs = \x -> lub b [f x | f <- fs]
lub (Pair a b) xys = (lub a xs, lub b ys) where (xs,ys) = unzip xys
lub (Sum a b) xs = foldr combine never xs
  where combine (Later x) (Later y) = Later $ combine x y
        combine x@Later{} y@Now{} = combine y x -- always put Now first
        combine (Now (Left x)) y = Now . Left $ lub a [x, eventually a fromLeft y]
          where fromLeft  (Left  q) = q
                fromLeft  (Right _) = error "Left/Right conflict"
        combine (Now (Right x)) y = Now . Right $ lub b [x, eventually b fromRight y]
          where fromRight (Right q) = q
                fromRight (Left  _) = error "Right/Left conflict"


-- BUT WHAT DOES IT __DO__??? (AKA examples/tests)

ex :: Int -> Expr Nat -> [Int]
ex n e = take n $ eval [] e

-- TODO:
-- f left = {0} union {x+1 for x in f right}
-- f rght = {x+1 for x in f left}

-- defining the bottom stream recursively works
simple :: Expr Nat
simple = EFix x (EVar x) where x = (Nat, "x")

-- defining the bottom function recursively works, remarkably!
dumb = EApp (EFix f (EVar f)) (ENat 0)
  where f = (Fun Nat Nat, "f")

plusOne :: Expr (Nat -> Nat)
plusOne = EVal (map (+1))

-- Stream of ever-increasing naturals: x = x + 1. Works.
omega :: Expr Nat
omega = EFix x (EApp plusOne (EVar x)) where x = (Nat, "x")

-- A step on the way: f x = 1 + f x
omega2 :: Expr Nat
omega2 = EApp (EFix f $ ELam x $ EApp plusOne $ EApp (EVar f) (EVar x))
              (ENat 0)
  where f = (Fun Nat Nat, "f")
        x = (Nat, "x")

at :: Int -> Expr (Nat -> a) -> Expr a
at n = flip EApp (ENat n)

-- Tests for ELub (ODO: at sum type)
-- f = (\x -> f (x + 1)) join (\x -> 4)
funjoin :: Expr Nat
funjoin = at 3 $ EFix f $ ELub ftp [ ELam x (EApp ef (EApp plusOne ex))
                                   , ELam x (ENat 4) ]
  where ftp = Fun Nat Nat
        f = (ftp, "f"); x = (Nat, "x")
        ef = EVar f; ex = EVar x

sumjoin :: Expr Nat
sumjoin = undefined

-- Evens & odds.
-- evenOdd (Left _)  = {0} lub {x + 1 for x in f (Right _)}
-- evenOdd (Right _) = {x + 1 for x in f (Left _)}
evenOdd :: Expr (Sum Nat Nat -> Set Nat)
evenOdd = EFix f $ ELam arg $ ECase (Set Nat) (EVar arg) (irr, case1) (irr, case2)
  where
    case1, case2, comp1 :: Expr (Set Nat)
    case1 = ELub (Set Nat) [ESet [ENat 0], comp1]
    comp1 = EFor (Set Nat)
                 (ef (EInj (Right (EVar irr))))
                 (x, ESet [EApp plusOne (EVar x)])
    case2 = EFor (Set Nat)
                 (ef (EInj (Left (EVar irr))))
                 (x, ESet [EApp plusOne (EVar x)])
    f = (Fun (Sum Nat Nat) (Set Nat), "f"); ef = EApp (EVar f)
    arg = (Sum Nat Nat, "arg")
    irr = (Nat, "irrelevant")
    x = (Nat, "x")

evens :: Expr (Set Nat)
evens = EApp evenOdd (EInj (Left (ENat 17)))

odds :: Expr (Set Nat)
odds = EApp evenOdd (EInj (Right (ENat 17)))

-- EXTREMELY SLOW. Don't take more than ~300 elements from this list.
nats :: Expr Nat
nats = EFor Nat (ELub (Set Nat) [evens, odds]) (x, EVar x)
  where x = (Nat, "x")

-- TODO: tests for pair types
-- TODO: tests for sum types
