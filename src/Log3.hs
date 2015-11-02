{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable #-}
module Log3 where

import qualified Data.Foldable as F
import Control.Monad
import Control.Monad.State
import Control.Monad.Trans.Either

import Types


type Env v = (Int, [(Int, v)])
emptyEnv :: Env a
emptyEnv = (0, [])

type Morph v = State (Env v)
type MMorph v = EitherT String (Morph v)


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

update :: Name -> a -> Morph a ()
update n v = modify $ \s -> update' s n v

update' (c, env) (N n) v =
  (c, insertList n v env)

look :: Name -> Morph a a
look (N n) = do
  gets $ fromJust . lookup n . snd
--look :: Env a -> Name -> a
--look env (N n) = fromJust $ lookup n $ snd env

store :: a -> Morph a Name
store v = do
  e <- get
  let (n, e') = store' e v
  put e'
  return n

store' :: Env v -> v -> (Name, Env v)
store' (c, env) val =
  (N c, (c+1, (c, val) : env))

data F a = F a | V Name
  deriving (Show, Eq, Ord, Functor, F.Foldable)

walk :: Name -> Morph Term (F Term)
walk n = do
  val <- look n
  case val of
    Eq n' -> walk n'
    Var -> return $ V n
    _ -> return $ F val

-- Recursively copy a form.
-- Everything gets a fresh name.
copy :: Name -> Morph Term Name
copy name = do
  form <- look name
  form' <- mapM copy form
  store form'

-- TODO delete
copyTest1 :: Morph Term Name
copyTest1 = do
  u <- store Var
  store Var
  store Var
  store Var
  v <- store Var
  p <- store $ Pair u v
  q <- copy p
  return q

unify :: Name -> Name -> MMorph Term ()
unify n1 n2 = do
  n1 <- lift $ walk n1
  n2 <- lift $ walk n2
  unify' n1 n2

forward n = Eq n

assert :: Bool -> String -> MMorph a ()
assert cond msg = if not cond then left msg else return ()

tag = fmap (const ())
tagEq x y = assert (((==) `on` tag) x y)
              ("pattern mismatch: " ) -- ++ sep x y)

children :: F.Foldable f => f a -> [a]
children = F.toList

childrenEq :: Term -> Term
           -> MMorph Term ()
childrenEq x y = do
  let xc = children x
  let yc = children y
  assert (length xc /= length yc) "ERROR differing children"
  mapM_ (uncurry unify) (zip xc yc)


unify' :: F Term -> F Term -> MMorph Term ()
unify' v1 v2
  | (V n1, V n2) <- (v1, v2)
  = if n2 > n1
    then lift $ update n2 (forward n1)
    else lift $ update n1 (forward n2)

  | V _ <- v2
  = unify' v2 v1

  | (V n1, F f) <- (v1, v2)
  = lift $ update n1 f

  | (F f1, F f2) <- (v1, v2)
  = do tagEq f1 f2
       childrenEq f1 f2

    
data Head a = H
  { p :: I a ()
  , e :: Env a
  }


exec s m = execState m s

single x = [x]

sigh (y, x) =
  case y of
    Left err -> Left err
    _ -> Right x

--runMM :: MMorph s a -> Env s -> (Env s, Either String a)
runMM m e = runState (runEitherT m) e

step :: ME (Head Term) -> Maybe [ME (Head Term)]
step (Left e) = Nothing
step (Right h) = case h of
  (H Stop _) -> Nothing
  (H (Unify n1 n2 cont) env) -> Just $ single $ do
   env' <- sigh $ runMM (unify n1 n2) env
   return $ H cont env'
  (H (Split is) env) -> Just [return (H i env) | i <- is]
 
  (H (Store val fcont) env) ->
    let (name, env') = runState (store val) env in
      Just $ [return (H (fcont name) env')]


run :: ME (Head Term) -> [ME (Head Term)]
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

type Pr = I Term ()
type P a = I Term a
type V = Name

p1 :: Pr
p1 = Store Var $ \n1 ->
     Store Var $ \n2 ->
     Unify n1 n2 Stop

st :: a -> I a Name
st x = Store x Pure

eq :: Name -> Name -> I a ()
eq x y = Unify x y (Pure ())

amb x y = Split [x, y]

p1' :: Pr
p1' = do
  n1 <- st Var `amb` st Nil
  n2 <- st Var
  eq n1 n2
  Stop

p2 :: Pr
p2 = do
  n1 <- st Var
  (h, t) <- cons n1
  Stop

-- Basics

sym :: Symbol -> Name -> P ()
sym sym n = do
  x <- st $ Sym sym
  eq x n

nil :: Name -> P ()
nil n = do
  x <- st Nil
  eq x n

cons :: Name -> P (V, V)
cons n = do
  l <- st Var
  r <- st Var
  c <- st (Pair l r)
  eq c n
  return $ (l, r)


