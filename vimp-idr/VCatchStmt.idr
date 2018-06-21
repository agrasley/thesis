module VCatchStmt

import V
import Dim

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
Mask : Type
Mask = (ErrCtx, ErrSt)

-- the variable state is a mapping from variable names to values
VarSt : Type
VarSt = List (VarName, Value)

-- Stateful global context
State : Type
State = (VCtx, VarSt, Mask)

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
data VLookup : VarName -> State -> Value -> Mask -> Type where

data InError : Dim -> Dim -> Type where

liftV : (a -> b) -> VOpt a -> VOpt b
liftV = liftA . liftA

liftV2 : (a -> b -> c) -> VOpt a -> VOpt b -> VOpt c
liftV2 = liftA2 . liftA2

-- big step semantics for arithmetic expressions
data BigAExpr : State -> AExpr -> Value -> Mask -> Type where
  -- literals are easy
  BigAN : BigAExpr (vctx,vst,m) (N i) (One (Just i)) m
  -- lookup variables in the environment, if they don't exist
  -- throw a builtin error
  BigAVar : VLookup x s v m -> BigAExpr s (Var x) v m
  -- add together two arithmetic expressions. evaluates left argument first.
  BigAAdd : BigAExpr (vctx,vst,m) l vl m' ->
            BigAExpr (vctx,vst,m') r vr m'' ->
            BigAExpr (vctx,vst,m) (Add l r) (liftV2 (+) vl vr) m''
  -- if both variants are in error states, don't do anything
  BigAChcErrs : InError (DAnd vctx dim) ectx ->
                InError (DAnd vctx (DNot dim)) ectx ->
                BigAExpr (vctx,vst,(ectx,est)) (AChc dim l r) (One Nothing) (ectx,est)
  -- if the left variant is in an error state
  BigAChcErrL : InError (DAnd vctx dim) ectx ->
                Not (InError (DAnd vctx (DNot dim)) ectx) ->
                BigAExpr ((DAnd vctx (DNot dim)),vst,(ectx,est)) r vr m ->
                BigAExpr (vctx,vst,(ectx,est)) (AChc dim l r) (Chc dim (One Nothing) vr) m
  -- if the right variant is in an error state
  BigAChcErrR : InError (DAnd vctx (DNot dim)) ectx ->
                Not (InError (DAnd vctx dim) ectx) ->
                BigAExpr ((DAnd vctx dim),vst,(ectx,est)) l vl m ->
                BigAExpr (vctx,vst,(ectx,est)) (AChc dim l r) (Chc dim vl (One Nothing)) m
  -- neither variant is in an error state
  BigAChc : Not (InError (DAnd vctx dim) ectx) ->
            Not (InError (DAnd vctx (DNot dim)) ectx') ->
            BigAExpr ((DAnd vctx dim),vst,(ectx,est)) l vl (ectx',est') ->
            BigAExpr ((DAnd vctx (DNot dim)),vst,(ectx',est')) r vr m'' ->
            BigAExpr (vctx,vst,m) (AChc dim l r) (Chc dim vl vr) m''

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

-- big step semantics for boolean expressions
data BigBExpr : State -> BExpr -> VOpt Bool -> Mask -> Type where
  -- literals are easy
  BigBB : BigBExpr (vctx,vst,m) (B b) (One (Just b)) m
  -- negation
  BigBNot : BigBExpr s b v m' -> BigBExpr s (Not b) (liftV Prelude.Bool.not v) m'
  -- and
  BigBAnd : BigBExpr (vctx,vst,m) l vl m' ->
            BigBExpr (vctx,vst,m') r vr m'' ->
            BigBExpr (vctx,vst,m) (And l r) (liftV2 VCatchStmt.and vl vr) m''

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
