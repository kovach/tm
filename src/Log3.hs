{-# LANGUAGE DeriveFunctor, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE DeriveFoldable #-}
module Log3 where

import qualified Data.Foldable as F
import Control.Monad


-- Names
newtype Name = N Int
  deriving (Eq, Ord)
instance Show Name where
  show (N n) = "#" ++ show n

toInt :: Name -> Int
toInt (N n) = n
incrName (N n) = (N (n+1))

type Env v = (Int, [(Int, v)])
emptyEnv = (0, [])

-- Stuff
first  f (a, b) = (f a, b)
second f (a, b) = (a, f b)
fromJust (Just x) = x
sep x y = show x ++ ", " ++ show y
on op f x y = (f x) `op` (f y)


type Error = String
type ME a = Either Error a

insertList n v [] = [(n,v)]
insertList n v ((n', _) : rest) | n == n' = (n', v) : rest
insertList n v (pair : rest) = pair : insertList n v rest

update (c, env) (N n) v =
  (c, insertList n v env)

look :: Env a -> Name -> a
look env (N n) = fromJust $ lookup n $ snd env

store (c, env) val =
  (N c, (c+1, (c, val) : env))

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

type Term = T Name

walk :: Env Term -> Name -> F Term
walk env n = do
  let val = look env n
  case val of
    Eq n' -> walk env n'
    Var -> V n
    _ -> F val

unify :: Env Term -> Name -> Name -> ME (Env Term)
unify env n1 n2 = 
  unify' env (walk env n1) (walk env n2)

forward n = Eq n

assert cond msg = if not cond then Left msg else return ()

tag = fmap (const ())
tagEq x y = assert (((==) `on` tag) x y)
              ("pattern mismatch: " ) -- ++ sep x y)

children :: F.Foldable f => f a -> [a]
children = F.toList

childrenEq env x y = do
  let xc = children x
  let yc = children y
  assert (length xc == length yc) "ERROR differing children"
  foldM (\env (n1, n2) -> unify env n1 n2) env (zip xc yc)


unify' env v1 v2
  | (V n1, V n2) <- (v1, v2)
  = return $ if n2 > n1
    then update env n2 (forward n1)
    else update env n1 (forward n2)

  | V _ <- v2
  = unify' env v2 v1

  | (V n1, F f) <- (v1, v2)
  = return $ update env n1 f

  | (F f1, F f2) <- (v1, v2)
  = do
    _ <- tagEq f1 f2
    childrenEq env f1 f2

    
data I a b
  = Unify Name Name (I a b)
  | Split [I a b]
  | Store a (Name -> I a b)
  | Pure b
  | Stop

data Head a = H
  { p :: I a ()
  , e :: Env a
  }

single x = [x]

step :: ME (Head Term) -> Maybe [ME (Head Term)]
step (Left e) = Nothing
step (Right h) = case h of
  (H Stop _) -> Nothing
  (H (Unify n1 n2 cont) env) -> Just $ single $ do
   env' <- unify env n1 n2
   return $ H cont env'
  (H (Split is) env) -> Just [return (H i env) | i <- is]
 
  (H (Store val fcont) env) ->
    let (name, env') = store env val in
      Just $ [return (H (fcont name) env')]


run h =
  case step h of
    Nothing -> [h]
    Just ts -> concatMap run ts

showMH (Left e) = e
showMH (Right (H _ e)) = show e

eval i = run $ Right $ H i emptyEnv
eval' = map showMH . eval

chk i = putStrLn $ init $ unlines $ map showMH $
  eval i

type P = I Term ()

p1 :: P
p1 = Store Var $ \n1 ->
     Store Var $ \n2 ->
     Unify n1 n2 Stop

st :: a -> I a Name
st x = Store x Pure

eq :: Name -> Name -> I a ()
eq x y = Unify x y (Pure ())

amb x y = Split [x, y]

p1' :: P
p1' = do
  n1 <- st Var `amb` st Nil
  n2 <- st Var
  eq n1 n2
  Stop

instance Functor (I Term) where
  fmap f m = undefined
instance Applicative (I Term) where
  pure = return
  f <*> x = do
    f <- f
    x <- x
    return $ f x

instance Monad (I Term) where
  return = Pure
  m >>= f =
    case m of
      Unify a b cont -> Unify a b (cont >>= f)
      Split conts -> Split (map (>>= f) conts)
      Store v fn -> Store v ((>>= f) . fn)
      Pure x -> f x
      Stop -> Stop

