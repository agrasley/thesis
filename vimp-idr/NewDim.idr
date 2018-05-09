module NewDim

import Data.SortedSet
import Env

%access public export

DimVar : Type
DimVar = String

data Clause : Type where
  DOr : SortedSet DimVar -> SortedSet DimVar -> SortedSet Bool -> Clause

data Dim : Type where
  DAnd : List Clause -> Dim
