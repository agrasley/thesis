module Dim

import Env

%access public export

DimVar : Type
DimVar = String

data Dim : Type where
  DLit : Bool -> Dim
  DRef : DimVar -> Dim
  DNot : Dim -> Dim
  DAnd : Dim -> Dim -> Dim
  DOr  : Dim -> Dim -> Dim

data DimHasVar : DimVar -> Dim -> Type where
  DimHere : DimHasVar x (DRef x)
  DimThereNot : DimHasVar x d -> DimHasVar x (DNot d)
  DimThereAndL : DimHasVar x d -> DimHasVar x (DAnd d d')
  DimThereAndR : DimHasVar x d' -> DimHasVar x (DAnd d d')
  DimThereOrL : DimHasVar x d -> DimHasVar x (DOr d d')
  DimThereOrR : DimHasVar x d' -> DimHasVar x (DOr d d')
