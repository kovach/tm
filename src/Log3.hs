{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable #-}
module Log3 where

import Data.List
import qualified Data.Foldable as F
import Control.Monad
import Control.Monad.State
import Control.Monad.Trans.Either

import Debug.Trace (trace)

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

-- Recursively copy a form. Everything gets a fresh name.
-- Equalities between existing subterms are preserved
shift n = do
  c <- shiftChildren [] n
  return $ fromJust $ lookup n c

type Context = [(Name, Name)]
shiftTerm :: Context -> Term -> Term
shiftTerm context term = fmap mod term
  where
    mod n | Just n' <- lookup n context = n'
    mod n = error "HUH"

shiftChildren :: Context -> Name -> Morph Term Context
shiftChildren context name = do
      case lookup name context of
        Nothing -> do
          form <- look name
          c' <- F.foldlM shiftChildren context form
          let form' = shiftTerm c' form
          name' <- store form'
          return $ (name, name') : c'
        Just _ -> return context

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
              ("fail. pattern mismatch:\n  "  ++ sep x y)

children :: F.Foldable f => f a -> [a]
children = F.toList

childrenEq :: Term -> Term
           -> MMorph Term ()
childrenEq x y = do
  let xc = children x
  let yc = children y
  assert (length xc == length yc)
         ("ERROR. differing children:\n  " ++ sep x y)
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

    
data Head a b = H
  { p :: I a b
  , e :: Env a }

sigh (y, x) =
  case y of
    Left err -> Left err
    _ -> Right x

--runMM :: MMorph s a -> Env s -> (Env s, Either String a)
runMM m e = runState (runEitherT m) e

-- TODO use Data.Set?
normalize :: [ME (Head Term a)] -> [ME (Head Term a)] 
normalize = sortOn thing
  where
    thing (Left _) = 0
    thing (Right (H _ (c, _))) = c

step :: ME (Head Term a) -> Maybe [ME (Head Term a)]
step (Left e) = Nothing
step (Right (H h env)) = case h of
  Stop -> Nothing
  Error e -> Nothing
  Pure x -> Nothing

  Unify n1 n2 cont -> Just $ single $ do
   env' <- sigh $ runMM (unify n1 n2) env
   return $ H cont env'
  Split is -> Just [return (H i env) | i <- is]

  Update name val cont ->
    let (_, env') = runState (update name val) env in
    Just $ [return (H cont env')]

  Copy x fcont ->
    let (name, env') = runState (shift x) env in
    Just $ [return (H (fcont name) env')]
  Store val fcont ->
    let (name, env') = runState (store val) env in
    Just $ [return (H (fcont name) env')]
  where
    single x = [x]


steps :: [ME (Head Term a)] -> [ME (Head Term a)]
steps [] = [] -- lol
steps es =
  let
    (as, bs) = split $ map run es
    as' = normalize $ concat as
    bs' = normalize $ concat bs
  in
  -- the as have fully normalized
  as' ++ steps bs'
  where
    -- Finished parses go to the left
    split = foldl' pick ([], [])
    pick (xs, ys) p@(True, x) = (x : xs, ys)
    pick (xs, ys) p@(False, y) = (xs, y : ys)

run :: ME (Head Term a) -> (Bool, [ME (Head Term a)])
run h =
  case step h of
    Nothing -> (True, [h])
    Just ts -> (False, ts)

isFailure :: Head Term a -> Bool
isFailure (H (Error e) _) = True
isFailure _ = False

takeN _ [] = []
takeN 0 _ = []
takeN n (t@(Left e) : r) = t : takeN n r
takeN n (t@(Right h) : r) | isFailure h = t : takeN n r
takeN n (Right x : r) = Right x : takeN (n-1) r

takeNOK _ [] = []
takeNOK 0 _ = []
takeNOK n (t@(Left e) : r) = takeNOK n r
takeNOK n (t@(Right h) : r) | isFailure h = takeNOK n r
takeNOK n (Right x : r) = Right x : takeNOK (n-1) r

showMH (Left e) = e
showMH (Right (H i e)) =
  ppI i ++ "\n" ++ show e

ppI (Error err) =
  "Parse error: " ++ err
ppI (Pure b) = "Result: " ++ show b ++ "."
ppI Stop = "Done."
ppI x = "Incomplete run."

eval :: Show a => Int -> P a -> [ME (Head Term a)]
eval n i = takeNOK n $ steps [Right $ H i emptyEnv]

chk n i =
  case eval n i of
    [] -> putStrLn "No Parse" ------- not needed really
    r -> do
      putStrLn $ "branches: " ++ show (length r) ++ "\n"
      putStrLn $ init $ unlines $
        map (++ "\n") $ filter ((> 0) . length) $ map showMH $ r

chm i =
  mapM_ (flip chk i) [0..8]

type Pr = I Term ()
type P a = I Term a
type V = Name

-- Instructions
st :: Term -> P Name
st x = Store x Pure

copy :: Name -> P Name
copy x = Copy x Pure

eq :: Name -> Name -> P ()
eq x y = Unify x y (Pure ())

up :: Name -> Term -> P ()
up n v = Update n v (Pure ())

amb :: P a -> P a -> P a
amb x y = Split [x, y]

failure :: String -> P a
failure = Error

-- Basics

var = st Var

sym :: Symbol -> Name -> P ()
sym sym n = do
  p <- st $ Sym sym
  eq p n

nil :: Name -> P ()
nil n = do
  p <- st Nil
  eq p n


pair :: Name -> P (V, V)
pair n = do
  l <- var
  r <- var
  c <- st (Pair l r)
  eq c n
  return $ (l, r)

empty :: Name -> P ()
empty n = do
  s <- ind n
  nil s

single :: Name -> P V
single n = do
  l <- var
  r <- st Nil
  p <- st (Pair l r)
  s <- ind n
  eq p s
  return $ l

ind :: Name -> P Name
ind n = do
  v <- var
  p <- st (Ind v)
  eq p n
  return v

push :: Name -> Name -> P ()
push val stack = do
  l <- ind stack
  l' <- st (Pair val l)
  up stack (Ind l')

pop :: Name -> P Name
pop stack = do
  l <- ind stack
  (t, r) <- pair l
  up stack (Ind r)
  return t

pleft :: Name -> P (Name, Name)
pleft n = do
  v <- var
  next <- var
  p <- st (LBind v next)
  eq p n
  return (v, next)

pright :: Name -> P (Name, Name)
pright n = do
  v <- var
  next <- var
  p <- st (RBind v next)
  eq p n
  return (v, next)

dereference :: Name -> Name -> P Name
dereference key dict =
  Split [end, top, bottom]
  where
    end = do
      nil dict
      failure $ "unknown symbol: " ++ show key
    top = do
      (h, _) <- pair dict
      (k, v) <- pair h
      eq k key
      return v
    bottom = do
      (_, t) <- pair dict
      dereference key t

dict_look :: Name -> Name -> P Name
dict_look key dict = do
  the_dict <- ind dict
  dereference key the_dict

-- Rules
parse_step :: Name -> Name -> Name -> P ()
parse_step dict l r = Split $
    [ p_node
    , p_clash
    , p_lbind
    , p_rbind
    , p_symbol
    , p_done
    ]

  where
    --p_noop = do
    --  r_noop <- pop r
    --  sym "CONTINUE" r_noop
    --  return ()
    p_symbol = do
      sym <- pop r
      binding <- dict_look sym dict
      rule <- copy binding
      push rule r

    p_lbind = do
      l_node <- pop l
      r_lbind <- pop r
      (t, next) <- pleft r_lbind
      eq t l_node
      push next r

    -- hmm
    p_rbind = do
      l_rbind <- pop l
      r_node <- pop r
      (t, next) <- pright l_rbind
      eq t r_node
      push next r

    p_clash = do
      l_rbind <- pop l
      r_lbind <- pop r
      _ <- pright l_rbind
      _ <- pleft r_lbind
      Error $ "CLASH: " ++ sep l_rbind r_lbind

    p_node = do
      r_node <- pop r
      push r_node l

    p_done = do
      nil r
      Stop

-- Program construction
mkRule :: [Name] -> [Name] -> Name -> P Name
mkRule lefts rights node = do
  r0 <- mkChain RBind rights node
  r1 <- mkChain LBind lefts r0
  return r1

mkChain :: (Name -> Name -> Term) -> [Name] -> Name -> P Name
mkChain _ [] n = return n
mkChain f (x : xs) n = do
  r <- st $ f x n
  mkChain f xs r

-- "Rules"
rec_rule sym mrule dict = do
  rule <- mrule
  label <- st (Sym sym)
  r <- st $ Pair label rule
  push r dict

r_eq = do
  x <- var
  mkRule [x] [x] x

r_plus = do
  l <- var
  r <- var
  p <- st $ Pair l r
  mkRule [l] [r] p

rec_eq dict = rec_rule "=" r_eq dict
rec_plus dict = rec_rule "+" r_plus dict
