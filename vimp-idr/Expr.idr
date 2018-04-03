module Expr

import Data.List
import Env

%access public export

-- Plain Imp Expressions

VarName : Type
VarName = String

data AExpr : Type where
  N : Int -> AExpr
  Var : VarName -> AExpr
  Add : AExpr -> AExpr -> AExpr

data BExpr : Type where
  B : Bool -> BExpr
  Not : BExpr -> BExpr
  And : BExpr -> BExpr -> BExpr
  Less : AExpr -> AExpr -> BExpr

State : List String -> Type
State xs = Env xs Int

data BigAExpr : State xs -> AExpr -> Int -> Type where
  BigN : BigAExpr s (N i) i
  BigVar : EnvLookup {x} p env i -> BigAExpr env (Var x) i
  BigAdd : BigAExpr s l i -> BigAExpr s r j -> BigAExpr s (Add l r) (i+j)

data BigBExpr : State xs -> BExpr -> Bool -> Type where
  BigB : BigBExpr s (B b) b
  BigNot : BigBExpr s be b -> BigBExpr s (Not be) (not b)
  BigAnd : BigBExpr s l b -> BigBExpr s r b' -> BigBExpr s (And l r) (b&&b')
  BigLess : BigAExpr s l i -> BigAExpr s r j -> BigBExpr s (Less l r) (i<j)

-- Testing Plain Imp Proofs

testBigN : BigAExpr s (N 7) 7
testBigN = BigN

{-
testBigVar : BigAExpr ([("x",1), ("y",2)],Var "y") 2
testBigVar = BigVar (VarThere VarHere)

testBigAdd : BigAExpr ([("x",1), ("y",2)], Add (N 7) (Var "y")) 9
testBigAdd = BigAdd testBigN testBigVar
-}
testBigB : BigBExpr s (B True) True
testBigB = BigB

testBigNot : BigBExpr s (Not (B True)) False
testBigNot = BigNot BigB

testBigAnd : BigBExpr s (And (B True) (B False)) False
testBigAnd = BigAnd BigB BigB

testBigLess : BigBExpr s (Less (N 2) (N 3)) True
testBigLess = BigLess BigN BigN
