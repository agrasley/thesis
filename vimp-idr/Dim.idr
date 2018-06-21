module Dim

import Data.SortedSet as S
import SSHelper
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

-- Satisfiable given a variable assignment
data SatWithCtx : Dim -> SortedSet DimVar -> Type where
  -- True is always sat
  SatLit : SatWithCtx (DLit True) e
  -- A variable is true if it exists in our assignment (all other variables are false)
  SatRef : SSElem x e -> SatWithCtx (DRef x) e
  -- The negation of an unsat term is sat
  SatNot : Not (SatWithCtx d e) -> SatWithCtx (DNot d) e
  -- If both subterms are sat, their conjunction is sat
  SatAnd : SatWithCtx d e -> SatWithCtx d' e -> SatWithCtx (DAnd d d') e
  -- If the left subterm is sat, its disjunction with anything is sat
  SatOrL : SatWithCtx d e -> SatWithCtx (DOr d d') e
  -- If the right subterm is sat, its disjunction with anything is sat
  SatOrR : SatWithCtx d' e -> SatWithCtx (DOr d d') e

-- Satisfiable
data Sat : Dim -> Type where
  -- Use a dependent pair to express if there exists some variable assigment
  -- that makes it sat, then it's sat
  MkSat : (s : SortedSet DimVar ** (SatWithCtx d s)) -> Sat d

-- Unsatisfiable
Unsat : Dim -> Type
Unsat d = Not (Sat d)
