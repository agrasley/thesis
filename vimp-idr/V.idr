module V

import Dim
import Sat

%access public export

data VTree : Type -> Type where
  One : a -> VTree a
  Chc : Dim -> VTree a -> VTree a -> VTree a

implementation Functor VTree where
  map f (One a) = One (f a)
  map f (Chc d l r) = Chc d (map f l) (map f r)

implementation Applicative VTree where
  pure = One
  (One f) <*> v = map f v
  (Chc d l r) <*> v = Chc d (l <*> v) (r <*> v)

implementation Monad VTree where
  (One a) >>= f = f a
  (Chc d l r) >>= f = Chc d (l >>= f) (r >>= f)

selTree : Dim -> VTree a -> VTree a
selTree _ v@(One _) = v
selTree d (Chc d' l r) =
  if implies d d' then
    selTree d l
  else if implies d (DNot d') then
    selTree d r
  else
    Chc d' (selTree d l) (selTree d r)
