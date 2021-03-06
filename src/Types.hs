{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable  #-}
module Types where

import qualified Data.Foldable as F
import qualified Data.Traversable as T

-- Names
newtype Name = N Int
  deriving (Eq, Ord)
instance Show Name where
  show (N n) = "#" ++ show n
toInt :: Name -> Int
toInt (N n) = n

type Symbol = String

data T a
  = Var
  | Eq a

  | Nil
  | Node

  | Lit Symbol
  | Symbol a
  | Token a

  | Ind a
  | Pair a a
  | Cons a a

  | Extension a a
  | Binding a a
  | Unbinding

  | Rule a a a
  | LBind a a
  | RBind a a

  deriving (Show, Eq, Ord, Functor, F.Foldable, T.Traversable)

type Term = T Name

data I a b
  = Pure b
  | Error String
  | Stop

  | Unify Name Name (I a b)
  | Split [I a b] -- Needs to be finite. TODO make it a pair?

  -- TODO separate mutation
  | Update Name a (I a b)

  | Store a (Name -> I a b)
  | Copy Name (Name -> I a b)
  deriving (Functor)

--TODO derived is ok?
--instance Functor (I Term) where
--  fmap f m = undefined
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
      Pure x -> f x
      Error e -> Error e
      Stop -> Stop
      Unify a b cont -> Unify a b (cont >>= f)
      Split conts -> Split (map (>>= f) conts)
      Update a v cont -> Update a v (cont >>= f)
      Store v fn -> Store v ((>>= f) . fn)
      Copy n fn -> Copy n ((>>= f) . fn)

