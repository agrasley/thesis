module VCatchStmt

import V
import Dim
import Data.Vect

%access public export

-- variable names are just strings
VarName : Type
VarName = String

VOpt : Type -> Type
VOpt a = VTree (Maybe a)

-- values are variational ints that might only exist in certain variants
Value : Type
Value = VOpt Int

-- the current variational context
VCtx : Type
VCtx = Dim

-- the error context is a boolean formula that tracks what variants are in error states
ErrCtx : Type
ErrCtx = Dim

-- the error state is a value that keeps track of the current error value in each variant, if
-- it exists
ErrSt : Type
ErrSt = Value

-- The mask handles error state
record Mask where
  constructor MkMask
  errCtx : ErrCtx
  errSt  : ErrSt

-- the variable state is a mapping from variable names to values
VarSt : Type
VarSt = List (VarName, Value)

-- Stateful global context
record State where
  constructor MkState
  vCtx : VCtx
  varSt : VarSt
  masks : Vect (S n) Mask

addToVCtx : Dim -> State -> State
addToVCtx d s = record {vCtx = (DAnd (vCtx s) d)} s

getErrCtx : State -> ErrCtx
getErrCtx s = errCtx (head (masks s))

-- variational arithmetic expression
data AExpr : Type where
  -- numeric literal
  N : Int -> AExpr
  -- numeric variable
  Var : VarName -> AExpr
  -- addition
  Add : AExpr -> AExpr -> AExpr
  -- choices
  AChc : Dim -> AExpr -> AExpr -> AExpr

-- TODO
data VLookup : VCtx -> VarName -> VarSt -> VTree Int -> Type where

data InError : VCtx -> ErrCtx -> Type where
{-

-- should this be state -> state or something more specific
data VUpdate : VarName -> Value -> State -> State -> Type where


insertMask : Dim -> VTree Int -> Mask -> Mask
-- TODO
-}

liftV : (a -> b) -> VOpt a -> VOpt b
liftV = liftA . liftA

liftV2 : (a -> b -> c) -> VOpt a -> VOpt b -> VOpt c
liftV2 = liftA2 . liftA2

mkOpt : VTree a -> VOpt a
mkOpt = map Just

-- big step semantics for arithmetic expressions
data BigAExpr : State -> AExpr -> Value -> Type where
  BigAN : BigAExpr s (N i) (One (Just i))
  BigAVar : VLookup (vCtx s) x (varSt s) vis ->
            BigAExpr s (Var x) (mkOpt vis)
  BigAAdd : BigAExpr s l vl ->
            BigAExpr s r vr ->
            BigAExpr s (Add l r) (liftV2 (+) vl vr)
  BigAChcELR : InError (DAnd (vCtx s) d) (getErrCtx s) ->
               InError (DAnd (vCtx s) (DNot d)) (getErrCtx s) ->
               BigAExpr s (AChc d l r) (One Nothing)
  BigAChcEL : InError (DAnd (vCtx s) d) (getErrCtx s) ->
              Not (InError (DAnd (vCtx s) (DNot d)) (getErrCtx s)) ->
              BigAExpr (addToVCtx (DNot d) s) r vr ->
              BigAExpr s (AChc d l r) (Chc d (One Nothing) vr)
  BigAChcER : Not (InError (DAnd (vCtx s) d) (getErrCtx s)) ->
              InError (DAnd (vCtx s) (DNot d)) (getErrCtx s) ->
              BigAExpr (addToVCtx d s) l vl ->
              BigAExpr s (AChc d l r) (Chc d vl (One Nothing))
  BigAChc : Not (InError (DAnd (vCtx s) d) (getErrCtx s)) ->
            Not (InError (DAnd (vCtx s) (DNot d)) (getErrCtx s)) ->
            BigAExpr (addToVCtx d s) l vl ->
            BigAExpr (addToVCtx (DNot d) s) r vr ->
            BigAExpr s (AChc d l r) (Chc d vl vr)

-- variational boolean expressions
data BExpr : Type where
  -- boolean literals
  B : Bool -> BExpr
  -- negation
  Not : BExpr -> BExpr
  -- conjunction
  And : BExpr -> BExpr -> BExpr
  -- numeric comparison
  Less : AExpr -> AExpr -> BExpr
  -- choices
  BChc : Dim -> BExpr -> BExpr -> BExpr

and : Bool -> Bool -> Bool
and True True = True
and _ _ = False

data BigBExpr : State -> BExpr -> VOpt Bool -> Type where
  BigBB : BigBExpr s (B b) (One (Just b))
  BigBNot : BigBExpr s b v ->
            BigBExpr s (Not b) (liftV Prelude.Bool.not v)
  BigBAnd : BigBExpr s l vl ->
            BigBExpr s r vr ->
            BigBExpr s (And l r) (liftV2 VCatchStmt.and vl vr)
  BigBLess : BigAExpr s l vl ->
             BigAExpr s r vr ->
             BigBExpr s (Less l r) (liftV2 (<) vl vr)
  BigBChcELR : InError (DAnd (vCtx s) d) (getErrCtx s) ->
               InError (DAnd (vCtx s) (DNot d)) (getErrCtx s) ->
               BigBExpr s (BChc d l r) (One Nothing)
  BigBChcEL : InError (DAnd (vCtx s) d) (getErrCtx s) ->
              Not (InError (DAnd (vCtx s) (DNot d)) (getErrCtx s)) ->
              BigBExpr (addToVCtx (DNot d) s) r vr ->
              BigBExpr s (BChc d l r) (Chc d (One Nothing) vr)
  BigBChcER : Not (InError (DAnd (vCtx s) d) (getErrCtx s)) ->
              InError (DAnd (vCtx s) (DNot d)) (getErrCtx s) ->
              BigBExpr (addToVCtx d s) l vl ->
              BigBExpr s (BChc d l r) (Chc d vl (One Nothing))
  BigBChc : Not (InError (DAnd (vCtx s) d) (getErrCtx s)) ->
            Not (InError (DAnd (vCtx s) (DNot d)) (getErrCtx s)) ->
            BigBExpr (addToVCtx d s) l vl ->
            BigBExpr (addToVCtx (DNot d) s) r vr ->
            BigBExpr s (BChc d l r) (Chc d vl vr)

-- variational statements
data Stmt : Type where
  -- noop
  Skip : Stmt
  -- assign the result of an expression to a variable
  Assign : VarName -> AExpr -> Stmt
  -- sequence statements
  Seq : Stmt -> Stmt -> Stmt
  -- if statements
  If : BExpr -> Stmt -> Stmt -> Stmt
  -- while loops
  While : BExpr -> Stmt -> Stmt
  -- throw an error
  Throw : AExpr -> Stmt
  -- try catch statements
  TryCatch : Stmt -> VarName -> Stmt -> Stmt
  -- choices
  SChc : Dim -> Stmt -> Stmt -> Stmt

data BigStmt : State -> Stmt -> State -> Type where
  -- skip doesn't change the state
  BigSSkip : BigStmt s Skip s
