module NewSat

import NewDim
import Env
import Data.SortedSet
import Data.List

%access public export

data SSElem : a -> SortedSet a -> Type where
  MkSSElem : Elem x (Data.SortedSet.toList ss) -> SSElem x ss

data ResResult : Type where
  ResT : ResResult
  ResEnv : SortedSet DimVar -> SortedSet DimVar -> ResResult

data Resolution : List Clause -> ResResult -> Type where
  ResStartT : SSElem True z -> Resolution [DOr x y z] ResT
  ResStartE : Resolution [DOr x y z] (ResEnv x y)
  ResTrue : Resolution xs res -> SSElem True z -> Resolution ((DOr x y z)::xs) res
  ResNextT : Resolution xs ResT -> Resolution ((DOr x y z)::xs) (ResEnv x y)
  ResNextE : Resolution xs (ResEnv a b) -> Resolution ((DOr x y z)::xs) (ResEnv (difference a y) (difference b x))

data SSNonEmpty : SortedSet a -> Type where
  MkSSNonEmpty : NonEmpty (Data.SortedSet.toList ss) -> SSNonEmpty ss

data Sat : Dim -> Type where
  SatT : Resolution xs ResT -> Sat (DAnd xs)
  SatE1 : SSNonEmpty x -> Resolution xs (ResEnv x y) -> Sat (DAnd xs)
  SatE2 : SSNonEmpty y -> Resolution xs (ResEnv x y) -> Sat (DAnd xs)

Unsat : Dim -> Type
Unsat d = Not (Sat d)
