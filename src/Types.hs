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
incrName (N n) = (N (n+1))

type Symbol = String

data T a
  = Var
  | Eq a

  | Nil
  | Sym Symbol

  | Ind a
  | Pair a a
  | Relation a a a -- ?

  | LEFT a a
  | RIGHT a a
  | DONE a

  deriving (Show, Eq, Ord, Functor, F.Foldable, T.Traversable)

type Term = T Name

data I a b
  = Unify Name Name (I a b)
  | Split [I a b]
  | Store a (Name -> I a b)
  | Pure b
  | Stop

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

