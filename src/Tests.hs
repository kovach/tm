module Tests where

import Log3
import Types


-- Tests
-- verbose example
p1' :: Pr
p1' = Store Var $ \n1 ->
     Store Var $ \n2 ->
     Unify n1 n2 Stop

p1 :: Pr
p1 = do
  n1 <- st Var `amb` st Nil
  n2 <- st Var
  eq n1 n2

p2 :: Pr
p2 = do
  n1 <- st Var
  (h, t) <- pair n1
  Stop

ct1 :: P Name
ct1 = do
  u <- st Var
  p <- st $ Pair u u
  copy p

ct2 :: P Name
ct2 = do
  u <- st Var
  st Var
  st Var
  st Var
  v <- st Var
  p <- st $ Pair u v
  copy p

-- Fully concrete dict
p3 :: Pr
p3 = do
  d <- var
  (p1, t0) <- pair d
  (p2, t1) <- pair t0
  nil t1
  (k1, v1) <- pair p1
  (k2, v2) <- pair p2
  lit "k1" k1
  lit "v1" v1
  lit "k2" k2
  lit "v2" v2

  ok <- var
  lit "k1" ok
  val <- dereference ok d

  Stop

-- Abstract dict
-- minimal solutions are
--   (k1,v1) : (k2, v2) : Var
--   (k2,v2) : (k1, v1) : Var
p4 = do
  d <- var

  k1 <- var
  k2 <- var
  lit "k1" k1
  lit "k2" k2
  v1 <- dereference k1 d
  v2 <- dereference k2 d

  return (d, v1, v2)

-- force ordering
p5 = do
  p@(d, _, _) <- p4
  (h, _) <- pair d
  (k, _) <- pair h
  lit "k2" k
  return p

p6 = do
  v <- st Nil
  s <- st (Ind v)
  v1 <- st $ Lit "1"
  v2 <- st $ Lit "2"
  push v2 s
  push v1 s
  pop s
  return s

p7 = do
  s <- var
  s0 <- ind s
  i1 <- pop s
  i2 <- pop s
  return (s, s0)

p8' = do
  v <- var
  l <- var
  n <- var
  r <- var
  val <- mkRule [l] [r] n
  eq v val
  return v

p8 = do
  s <- var
  (a, b) <- pleft s
  _ <- pright b
  return s

setup = do
  l <- var
  r <- var
  dict <- var
  names <- var

  l0 <- ind l
  r0 <- ind r
  d0 <- ind dict
  n0 <- ind names

  return ((n0, dict, l, r), (d0, l0, r0))

done :: Name -> Name -> P Name
done l r = do
  empty r
  v <- single l
  value v
  return v

p9 = do
  ((ns, dict, l, r), (d0, l0, r0)) <- setup
  parse_step ns dict l r
  parse_step ns dict l r
  parse_step ns dict l r
  result <- done l r
  return (result, dict, l0, r0)


standard_init = do
  p@((names, dict, l, r), _) <- setup
  empty dict
  empty l
  empty r
  empty names

  mapM (flip (uncurry rec_rule) dict) rules

  return p

repl 0 m = return ()
repl n m = m >> repl (n-1) m

doCounter = True
pfix names dict l r c = Split [d, again]
  where
    d = do
      res <- done l r
      return res
    again = do
      v <- if doCounter
             then do
               v <- var
               i <- st $ Ind v
               eq c i
               return v
             else return c
      parse_step names dict l r
      pfix names dict l r v

-- TODO return count
runp m = do
  ((names, dict, l, r), (d0, l0, r0)) <- standard_init
  counter <- var
  m dict l r
  res <- pfix names dict l r counter
  count <- nat2int counter
  return (count, res, dict, l0, r0)

p10 dict l r = do
  pl <- word "="
  n0 <- word "a"
  n1 <- word "a"
  push n1 r
  push pl r
  push n0 r

p10' dict l r = do
  op <- word "="
  n0 <- word "a"
  n1 <- word "a"
  push n1 r
  lst <- storeList [n0, op]
  push lst r

p10'' dict l r = program "a = a" r

p11 dict l r = program "[ x a ]" r
p12 dict l r = do
  n <- st Node
  op <- word "]"
  x <- word "x"
  push op r
  push x r
  push n r

defp s _ _ = program s
