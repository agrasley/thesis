module Sat

import Dim
import Data.SortedSet
import Env
import Data.List

%access public export

-- Type level sat

-- sorted set membership proofs
data SSElem : a -> SortedSet a -> Type where
  -- convert the set to a list and then use the builtin list membership proof
  MkSSElem : Elem x (Data.SortedSet.toList ss) -> SSElem x ss

-- Resolution results
data ResResult : Type where
  -- The resolution is universally true
  ResT : ResResult
  -- The resolution is true given an environment of positive and negative variables
  ResEnv : SortedSet DimVar -> SortedSet DimVar -> ResResult

-- Proof that a list of clauses produces a particular ResResult
data Resolution : List Clause -> ResResult -> Type where
  -- The last element of the list contains a True literal and is universally true
  ResStartT : SSElem True z -> Resolution [CNFOr x y z] ResT
  -- The last element of the list is true given a variable environment
  ResStartE : Resolution [CNFOr x y z] (ResEnv x y)
  -- Adding a clause that is universally true doesn't change the result
  ResTrue : Resolution xs res -> SSElem True z -> Resolution ((CNFOr x y z)::xs) res
  -- If all previous clauses are universally true, we start the maintaining the environment here
  ResNextT : Resolution xs ResT -> Resolution ((CNFOr x y z)::xs) (ResEnv x y)
  -- We remove contradictory members of the variable environments when combining two environments
  ResNextE : Resolution xs (ResEnv a b) -> Resolution ((CNFOr x y z)::xs) (ResEnv (difference a y) (difference b x))


-- Proof that a sorted set is non empty
data SSNonEmpty : SortedSet a -> Type where
  -- turn it into a list and prove the list is non empty
  MkSSNonEmpty : NonEmpty (Data.SortedSet.toList ss) -> SSNonEmpty ss

-- Proof that a boolean formula in CNF is satisfiable
data Sat : CNF -> Type where
  -- It's universally true
  SatT : Resolution xs ResT -> Sat (CNFAnd xs)
  SatE1 : SSNonEmpty x -> Resolution xs (ResEnv x y) -> Sat (CNFAnd xs)
  SatE2 : SSNonEmpty y -> Resolution xs (ResEnv x y) -> Sat (CNFAnd xs)

Unsat : CNF -> Type
Unsat d = Not (Sat d)
