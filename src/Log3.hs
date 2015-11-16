{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable #-}
module Log3 where

import Data.List
import qualified Data.Foldable as F
import Control.Monad
import Control.Monad.State
import Control.Monad.Trans.Either

import Debug.Trace (trace)

import Data.Char (isUpper)

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

  Unify n1 n2 cont -> Just $ ret $ do
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
    ret x = [x]


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

takeNOK c _ [] = []
takeNOK c 0 _ = []
takeNOK c n (t@(Left e) : r) = takeNOK (c+1) n r
takeNOK c n (t@(Right h) : r) | isFailure h = takeNOK (c+1) n r
takeNOK c n (Right x : r) = (c, Right x) : takeNOK (c+1) (n-1) r

showMH (_, Left e) = e
showMH (c, Right (H i e)) =
  "DEPTH: " ++ show c ++ "\n" ++ ppI i ++ "\n" ++ show e

ppI (Error err) =
  "Parse error: " ++ err
ppI (Pure b) = "Result: " ++ show b ++ "."
ppI Stop = "Done."
ppI x = "Incomplete run."

eval :: Show a => Int -> P a -> [(Int, ME (Head Term a))]
eval n i = takeNOK 0 n $ steps [Right $ H i emptyEnv]

chk n i =
  case eval n i of
    [] -> putStrLn $ "No Parse."
    r -> do
      putStrLn $ init $ unlines $
        map (++ "\n") $ filter ((> 0) . length) $ map showMH $ r

chm i =
  mapM_ (flip chk i) [0..8]

type Pr = I Term ()
type P a = I Term a

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
-- TODO better naming scheme
-- do this:
-- mk_foo :: name -> P Term
-- match_1 :: (name -> P Term) -> name -> P name
-- ?

var = st Var

lit :: Symbol -> Name -> P ()
lit sym n = do
  p <- st $ Lit sym
  eq p n

sym :: Symbol -> P Name
sym s = do
  l <- st $ Lit s
  st $ Symbol l

word :: Symbol -> P Name
word n = do
  l <- st $ Lit n
  st $ Token l

symbol :: Name -> P Name
symbol n = do
  v <- var
  p <- st (Symbol v)
  eq p n
  return v

token :: Name -> P Name
token n = do
  v <- var
  p <- st (Token v)
  eq p n
  return v

nil :: Name -> P ()
nil n = do
  p <- st Nil
  eq p n

tuple :: Name -> P (Name, Name)
tuple n = do
  l <- var
  r <- var
  p <- st (Pair l r)
  eq p n
  return $ (l, r)

pair :: Name -> P (Name, Name)
pair n = do
  l <- var
  r <- var
  c <- st (Cons l r)
  eq c n
  return $ (l, r)

empty :: Name -> P ()
empty n = do
  s <- ind n
  nil s

single :: Name -> P Name
single n = do
  l <- var
  r <- st Nil
  p <- st (Cons l r)
  s <- ind n
  eq p s
  return $ l

singleton :: Name -> P Name
singleton n = do
  l <- var
  r <- st Nil
  p <- st (Cons l r)
  eq p n
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
  l' <- st (Cons val l)
  up stack (Ind l')

amb_ :: P a -> P b -> P ()
amb_ a b = amb (a >> return ()) (b >> return ())

-- Push onto "rope"
push1 :: Name -> Name -> P ()
push1 val stack = amb cell top
  where
    cell = do
      list <- pop stack
      _ <- nil list `amb_` pair list
      l' <- st (Cons val list)
      push l' stack
    top = push val stack

-- Pop from "rope"
pop1 :: Name -> P Name
pop1 stack = amb top cell
  where
    top = pop stack

    cell = do
      list <- pop stack
      let
        cell_O = do
          nil list
          pop stack
        cell_S = do
          (t, r) <- pair list
          push r stack
          return t

      amb cell_O cell_S

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

extend :: Name -> Name -> P Name
extend k v = do
  st (Extension k v)

extension :: Name -> P (Name, Name)
extension n = do
  k <- var
  v <- var
  p <- extend k v
  eq p n
  return (k, v)

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
    --, p_name
    , p_clash
    , p_lbind
    , p_rbind
    , p_symbol
    , p_extend
    , p_sub
    ]

  where
    p_symbol = do
      sym <- pop1 r
      binding <- dict_look sym dict
      rule <- copy binding
      push rule r

    --p_name = do
    --  tk <- pop1 r
    --  s <- token tk
    --  v <- st $ Symbol s
    --  push v r

    p_lbind = do
      l_node <- pop1 l
      r_lbind <- pop1 r
      (t, next) <- pleft r_lbind
      eq t l_node
      push next r

    p_rbind = do
      l_rbind <- pop1 l
      r_node <- pop1 r
      (t, next) <- pright l_rbind
      eq t r_node
      push next r

    p_clash = do
      l_rbind <- pop1 l
      r_lbind <- pop1 r
      _ <- pright l_rbind
      _ <- pleft r_lbind
      Error $ "CLASH: " ++ sep l_rbind r_lbind

    p_node = do
      r_node <- pop1 r
      amb_ (value r_node) (pright r_node)
      push1 r_node l

    p_extend = do
      r_ext <- pop1 r
      (k, v) <- extension r_ext
      -- TODO make dict a list of Extensions
      p <- st (Cons k v)
      push p dict

    p_sub = do
      rn <- pop1 r
      p <- st Node
      eq p rn
      n <- st Nil
      push1 n l

value :: Name -> P ()
value name = do
  (symbol name) `amb_` (tuple name)

    --p_noop = do
    --  r_noop <- pop r
    --  sym "CONTINUE" r_noop
    --  return ()

    --p_done = do
    --  nil r
    --  Stop

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
  token <- word sym
  r <- st $ Cons token rule
  push r dict

r_eq = do
  x <- var
  p <- st $ Pair x x
  mkRule [x] [x] x

r_plus = do
  l <- var
  r <- var
  p <- st $ Pair l r
  mkRule [l] [r] p

r_lbracket = do
  v <- var
  arg <- st $ Token v
  meaning <- var
  op <- extend arg meaning
  n <- st Node
  out <- storeList [op, n]
  --out <- storeList [op]
  mkRule [] [arg] out

r_rbracket = do
  p <- var
  v <- singleton p
  value v
  mkRule [p] [] v

rec_eq = rec_rule "=" r_eq
rec_plus = rec_rule "+" r_plus
rec_lbracket = rec_rule "[" r_lbracket
rec_rbracket = rec_rule "]" r_rbracket

rules =
  [ ("=", r_eq)
  , ("+", r_plus)
  , ("[", r_lbracket)
  , ("]", r_rbracket)
  ]

-- [x: x is a thing]
-- '[' -> do
  -- push Nil
  -- x <- rbind
  -- push (x, Var) dict
-- ']' -> do
  -- stack <- lbind
  -- res <- single stack (or empty?)
  -- ?? res


-- Stuff
nat2int :: Name -> P Int
nat2int n = amb o succ
  where
    o = nil n >> return 0
    succ = do
      n' <- ind n
      v <- nat2int n'
      return $ 1 + v

storeList :: [Name] -> P Name
storeList [] = st Nil
storeList (x : xs) = do
  r <- storeList xs
  c <- st (Cons x r)
  return c

program :: String -> Name -> P ()
program str r = do
    ops <- mapM constr $ words str
    mapM_ (flip push r) (reverse ops)
  where
    constr t@(c : _) | isUpper c = sym t
    constr t = word t
