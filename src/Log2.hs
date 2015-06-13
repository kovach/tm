{-# LANGUAGE DeriveFunctor, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE DeriveFoldable #-}
module Log2 where

import Prelude hiding (fail)
import qualified Data.Foldable as F

import Debug.Trace (trace)

-- Names
newtype Name = N Int
  deriving (Eq, Ord)
instance Show Name where
  show (N n) = "#" ++ show n

toInt :: Name -> Int
toInt (N n) = n
incrName (N n) = (N (n+1))

-- Base Monad
type Env v = [(Int, v)]
type C v = (Int, Env v)
type Error = String
data M v a = M { runM :: C v -> [(Either Error a, C v)] }

-- Stuff
first  f (a, b) = (f a, b)
second f (a, b) = (a, f b)
fromJust (Just x) = x
sep x y = show x ++ ", " ++ show y
on op f x y = (f x) `op` (f y)

-- Instances
instance Functor (M s) where
  fmap f m = M $ \s -> map (first $ fmap f) $ runM m s

instance Applicative (M s) where
  pure a = M $ \s -> [(Right a, s)]
  f <*> x = do
    f <- f
    x <- x
    return $ f x

instance Monad (M s) where
  --return a = M $ \s -> [(a, s)]
  m >>= f = M $ \s ->
    let pairs = runM m s
        ap (a, s') =
          case a of
            Left e -> [(Left e, s')]
            Right x -> runM (f x) s'
    in F.foldl' interleave2 (return []) $ map ap pairs

head' [] = []
head' (x : xs) = [x]
tail' [] = [[]]
tail' [x] = [[]]
tail' (x : xs) = [xs]
interMany xs = concatMap head' xs ++ interMany (concatMap tail' xs)

-- Output
run :: M s a -> [(Either Error a, C s)]
run m = runM m (0, [])

runf :: Functor f => M (f Name) a -> [(Either Error a, Env (f Int))]
runf m =
  let pairs = run m
      fixp (val, (_, env)) = (val, map (second (fmap toInt)) env)
  in
    map fixp pairs

runf' :: Functor f => M (f Name) (f Name) -> [(Either Error (f Int), Env (f Int))]
runf' = map (first (fmap $ fmap toInt)) . runf

evalf :: M s a -> [Either Error a]
evalf = map fst . run

-- Monad Basics
get :: M s (C s)
get = M $ \s -> [(Right s, s)]

put :: (C s) -> M s ()
put s = M $ \_ -> [(Right (), s)]

store :: s -> M s Name
store v = do
  (c, env) <- get
  let l = c+1
  put (l, (l, v) : env)
  return (N l)

curr :: M s Name
curr = do
  (c, _) <- get
  return (N c)

insertList n v [] = [(n,v)]
insertList n v ((n', _) : rest) | n == n' = (n', v) : rest
insertList n v (pair : rest) = pair : insertList n v rest

update :: Name -> s -> M s ()
update (N n) v = do
  (c, env) <- get
  put (c, insertList n v env)

look :: Name -> M s s
look (N n) = do
  (_, e) <- get
  return $ fromJust $ lookup n e

-- BAD
interleave0 [] ys = ys
interleave0 xs [] = xs
interleave0 (x : xs) (y : ys) = x : y : interleave0 xs ys

interL [] ys = ys
interL (x : xs) ys = x : interR xs ys
interR xs [] = xs
interR xs (y : ys) = y : interL xs ys
interleave2 = interL

interleave1 = (++)

interleave = interleave2

amb :: M s a -> M s a -> M s a
amb a b = M $ \s -> interleave (runM a s) (runM b s)

fail :: Error -> M s a
fail err = M $ \s -> [(Left err, s)]

assert :: Bool -> Error -> M s ()
assert cond msg = if not cond then fail msg else return ()

exit :: M s a
exit = M $ \s -> []


-- Unification

-- types
data F a = F a | V Name
  deriving (Show, Eq, Ord, Functor, F.Foldable)

type Symbol = String

data T a
  = Var
  | Eq a

  | Nil
  | Sym Symbol
  | Pair a a
  | Relation a a a

  | Ptr a
  deriving (Show, Eq, Ord, Functor, F.Foldable)

tagStr :: T a -> String
tagStr e = case e of
  Var -> "var"
  Eq _ -> "eq"
  Nil -> "nil"
  Sym s -> "#" ++ s
  Pair _ _ -> "pair"
  Relation _ _ _ -> "rel"
  Ptr _ -> "ptr"

type TM = M (T Name)
type Term = T Name
type MT = M Term Name

-- name resolve
-- TODO remove ns
walk ns n | n `elem` ns = error $ "loop: " ++ show ns
walk ns n = do
  val <- look n
  case val of
    Eq n' -> walk (n : ns) n'
    Var -> return $ V n
    _ -> return $ F val

-- base case
tag = fmap (const ())
tagEq x y = assert (((==) `on` tag) x y)
              ("pattern mismatch: " ) -- ++ sep x y)

children :: F.Foldable f => f a -> [a]
children = F.toList

childrenEq x y = do
  let xc = children x
  let yc = children y
  assert (length xc == length yc) "ERROR differing children"
  mapM (uncurry unify) (zip xc yc)

forward n = Eq n

unify :: Name -> Name -> TM ()
unify n1 n2 = do
  v1 <- walk [] n1
  v2 <- walk [] n2
  unify' v1 v2

unify' v1 v2
  | (V n1, V n2) <- (v1, v2)
  = if n2 > n1
    then update n2 (forward n1)
    else update n1 (forward n2)

  | V _ <- v2
  = unify' v2 v1

  | (V n1, F f) <- (v1, v2)
  = update n1 f

  | (F f1, F f2) <- (v1, v2)
  = do
    _ <- tagEq f1 f2
    _ <- childrenEq f1 f2
    return ()


var :: MT
var = store Var

nil :: MT
nil = store Nil

symbol :: Symbol -> MT
symbol sym = store (Sym sym)

pair :: MT -> MT -> MT
pair a b = do
  a <- a
  b <- b
  store $ Pair a b

relation :: MT -> MT -> MT -> MT
relation a r b = do
  a <- a
  r <- r
  b <- b
  store $ Relation a r b

ptr v = do
  v <- v
  store $ Ptr v

match :: MT -> Name -> TM Term
match p n = do
  p <- p
  unify n p
  look p

isNil :: Name -> TM Term
isNil name = match nil name

isPair :: Name -> TM Term
isPair name = match (pair var var) name

isPtr :: Name -> TM Term
isPtr name = match (ptr var) name

isSym :: Symbol -> Name -> TM Term
isSym sym name = match (symbol sym) name

push :: Name -> Name -> TM ()
push val stack = do
  Ptr top <- isPtr stack
  top' <- store (Pair val top)
  update stack (Ptr top')

pop :: Name -> MT
pop stack = do
  Ptr p <- isPtr stack
  Pair h t <- isPair p
  update stack (Ptr t)
  return h

empty :: Name -> TM Term
empty stack = do
  Ptr p <- isPtr stack
  isNil p


tops :: Name -> Name -> TM ()
tops n1 n2 = do
  h1 <- pop n1
  h2 <- pop n2
  unify h1 h2
  return ()

bind :: Symbol -> Name -> Name -> TM ()
bind label val stack = do
  l <- store $ Sym label
  p <- store $ Pair l val
  push p stack

value :: Symbol -> Name -> TM Name
value sym stack = do
  Ptr s <- isPtr stack
  findV sym s

trcurr s m = do
  c <- curr
  trace (s ++ ":" ++ show c) $ m

findV :: Symbol -> Name -> TM Name
findV sym stack = (onTop `amb` keepLooking)
  where
    onlyThis = trcurr "1" $ do
      Pair h t <- isPair stack
      Pair label value <- isPair h
      isSym sym label
      isNil t
      return value
    onTop = trcurr "2" $ do
      Pair h _ <- isPair stack
      Pair label value <- isPair h
      isSym sym label
      return value
    keepLooking = trcurr "3" $ do
      Pair _ t <- isPair stack
      findV sym t


-- Testing
m4 = do
  v <- (ptr nil)
  v1 <- var
  v2 <- var
  push v1 v
  push v2 v
  isNil v1
  isPtr v

m1 = do
  v <- ptr var
  match (ptr (pair nil nil)) v

m2 = do
  v1 <- var
  v2 <- var
  tops v1 v2
  empty v1
  empty v2
  look v1

m3 = do
  env <- ptr nil
  v1 <- var
  v2 <- var
  bind "x" v1 env
  bind "y" v2 env
  unify v1 v2
  isNil v1
  return env

m5 = do
  env <- ptr nil
  venv <- ptr var
  v1 <- symbol "x-val"
  v2 <- symbol "y-val"
  bind "x" v1 env
  bind "y" v2 env
  v1' <- value "x" venv
  v2' <- value "y" venv
  --unify v1' v2'
  --t <- pop venv
  --Pair s _ <- isPair t
  --isSym "x" s
  return venv

m6 = do
  venv <- ptr var
  v <- var
  bind "x" v venv
  _ <- value "x" venv
  look venv
  
takeRights :: Int -> [Either a b] -> [b]
takeRights 0 _ = []
takeRights _ [] = []
takeRights n (Right x : xs) = x : takeRights (n-1) xs
takeRights n (Left x : xs) = takeRights n xs

takeRight = takeRights 1

findSome :: Int -> [(Either a b, c)] -> [Either a (b, c)]
findSome 0 _ = []
findSome n ((Left v, _) : vs) =
  Left v : findSome n vs
findSome _ [] = []
findSome n ((Right v, env) : vs) =
  Right (v, env) : findSome (n-1) vs

showV (Left err) = "ERR: " ++ err
showV (Right (v, e)) = unlines (show v : map show e)

ch :: Int -> TM Term -> IO ()
ch n = mapM_ putStrLn . map showV . (findSome n) . take 20 . runf'

chk = ch 1

pr n m = takeRights n $ evalf $ m >>= pp

-- Printing
data Tree = Node Name String [Tree]

sep1 a b = show a ++ ", " ++ b
instance Show Tree where
  show n = show' "" n

show' n (Node name str ts) = n ++ (init $ unlines $ [sep1 name str] ++ (map (show' ("  " ++ n)) ts))

pp :: Name -> TM Tree
pp name = do
  val <- look name
  branches <- mapM pp $ children val
  return $ Node name (tagStr val) branches
