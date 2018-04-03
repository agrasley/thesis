module Dim

import Env
import Data.List

%access public export

DimVar : Type
DimVar = String

data Dim : Type where
  DLit : Bool -> Dim
  DRef : DimVar -> Dim
  DNot : Dim -> Dim
  DAnd : Dim -> Dim -> Dim
  DOr  : Dim -> Dim -> Dim

SatEnv : List DimVar -> Type
SatEnv xs = Env xs Bool

data Sat : SatEnv xs -> Dim -> Type where
  SatT : Sat env (DLit True)
  SatR : EnvLookup {x} p env True -> Sat env (DRef x)
  SatN : Not (Sat env d) -> Sat env (DNot d)
  SatA : Sat env l -> Sat env r -> Sat env (DAnd l r)
  SatOL : Sat env l -> Sat env (DOr l r)
  SatOR : Sat env r -> Sat env (DOr l r)

{-
infixr 10 |=>|
data (|=>|) : Dim -> Dim -> Type where
  ImpTT : x |=>| DLit True
  ImpTT 
-}
