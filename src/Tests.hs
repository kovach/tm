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
  Stop

p2 :: Pr
p2 = do
  n1 <- st Var
  (h, t) <- pair n1
  Stop

copyTest2 :: Pr
copyTest2 = do
  u <- st Var
  st Var
  st Var
  st Var
  v <- st Var
  p <- st $ Pair u v
  q <- copy p
  Stop

-- Fully concrete dict
p3 :: Pr
p3 = do
  d <- var
  (p1, t0) <- pair d
  (p2, t1) <- pair t0
  nil t1
  (k1, v1) <- pair p1
  (k2, v2) <- pair p2
  sym "k1" k1
  sym "v1" v1
  sym "k2" k2
  sym "v2" v2

  ok <- var
  sym "k1" ok
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
  sym "k1" k1
  sym "k2" k2
  v1 <- dereference k1 d
  v2 <- dereference k2 d

  return (d, v1, v2)

-- force ordering
p5 = do
  p@(d, _, _) <- p4
  (h, _) <- pair d
  (k, _) <- pair h
  sym "k2" k
  return p

p6 = do
  v <- st Nil
  s <- st (Ind v)
  v1 <- st $ Sym "1"
  v2 <- st $ Sym "2"
  push v2 s
  push v1 s
  pop s
  return s
