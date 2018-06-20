module Dim

import Data.SortedSet as S
import Env

%access public export

DimVar : Type
DimVar = String

-- Dimensions are a boolean algebra
data Dim : Type where
  -- boolean literals
  DLit : Bool -> Dim
  -- boolean variables
  DRef : DimVar -> Dim
  -- negation
  DNot : Dim -> Dim
  -- conjunction
  DAnd : Dim -> Dim -> Dim
  -- disjunction
  DOr : Dim -> Dim -> Dim

-- negation normal form
data NNF : Type where
  -- boolean literals
  NNFLit : Bool -> NNF
  -- positive variables
  NNFRef : DimVar -> NNF
  -- negative variables
  NNFNot : DimVar -> NNF
  -- conjunction
  NNFAnd : NNF -> NNF -> NNF
  -- disjunction
  NNFOr : NNF -> NNF -> NNF

-- boolean algebra to negation normal form
data DimToNNF : Dim -> NNF -> Type where
  -- eliminate double negatives
  DoubleNeg : DimToNNF d n -> DimToNNF (DNot (DNot d)) n
  -- use demorgan's law to push negation down in conjunctions
  DMAnd : DimToNNF (DNot l) l' -> DimToNNF (DNot r) r' -> DimToNNF (DNot (DAnd l r)) (NNFOr l' r')
  -- use demorgan's law to push negation down in disjunctions
  DMOr : DimToNNF (DNot l) l' -> DimToNNF (DNot r) r' -> DimToNNF (DNot (DOr l r)) (NNFAnd l' r')
  -- and corresponds to and when not negated
  DTNAnd : DimToNNF l l' -> DimToNNF r r' -> DimToNNF (DAnd l r) (NNFAnd l' r')
  -- or corresponds to or when not negated
  DTNOr : DimToNNF l l' -> DimToNNF r r' -> DimToNNF (DOr l r) (NNFOr l' r')
  -- negation of a literal we just perform the negation directly
  DTNNotLit : DimToNNF (DNot (DLit b)) (NNFLit (Prelude.Bool.not b))
  -- negation of a variable
  DTNNotRef : DimToNNF (DNot (DRef x)) (NNFNot x)
  -- literals
  DTNLit : DimToNNF (DLit b) (NNFLit b)
  -- variables
  DTNRef : DimToNNF (DRef x) (NNFRef x)

-- A clause in conjunctive normal form
data Clause : Type where
  -- takes arguments for sets of positive variables, negative variables,
  -- and literals, which are all in disjunction with each other
  CNFOr : SortedSet DimVar -> SortedSet DimVar -> SortedSet Bool -> Clause

-- Conjunctive normal form
data CNF : Type where
  -- CNF is an and of ors
  CNFAnd : List Clause -> CNF

singleton : Ord a => a -> SortedSet a
singleton a = fromList [a]

data NNFToCNF : NNF -> CNF -> Type where
  -- literals
  NTCLit : NNFToCNF (NNFLit b) (CNFAnd [CNFOr S.empty S.empty (Dim.singleton b)])
  -- positive variables
  NTCRef : NNFToCNF (NNFRef x) (CNFAnd [CNFOr (Dim.singleton x) S.empty S.empty])
  -- negative variables
  NTCNot : NNFToCNF (NNFNot x) (CNFAnd [CNFOr S.empty (Dim.singleton x) S.empty])
  -- conjunction is just concatentation of the two subterms' results
  NTCAnd : NNFToCNF nl (CNFAnd cl) -> NNFToCNF nr (CNFAnd cr) -> NNFToCNF (NNFAnd nl nr) (CNFAnd (cl++cr))
  -- disjunction without conjunction is union
  NTCOr : NNFToCNF n (CNFAnd [CNFOr x y z]) -> NNFToCNF n' (CNFAnd [CNFOr x' y' z']) -> NNFToCNF (NNFOr n n') (CNFAnd [CNFOr (S.union x x') (S.union y y') (S.union z z')])
  -- push disjunction down
  NTCOrAndL : NNFToCNF (NNFAnd (NNFOr x z) (NNFOr y z)) c -> NNFToCNF (NNFOr (NNFAnd x y) z) c
  NTCOrAndR : NNFToCNF (NNFAnd (NNFOr x y) (NNFOr x z)) c -> NNFToCNF (NNFOr x (NNFAnd y z)) c
