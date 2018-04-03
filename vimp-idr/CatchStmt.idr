module CatchStmt

import Expr
import Data.List
import Env

%access public export

data Stmt : Type where
  Skip : Stmt
  Assign : VarName -> AExpr -> Stmt
  Seq : Stmt -> Stmt -> Stmt
  If : BExpr -> Stmt -> Stmt -> Stmt
  While : BExpr -> Stmt -> Stmt
  Throw : AExpr -> Stmt
  TryCatch : Stmt -> VarName -> Stmt -> Stmt

ErrCode : Type
ErrCode = Int

data BigStmt : Maybe ErrCode -> State xs -> Stmt -> Maybe ErrCode -> State xs' -> Type where
  BigErr : BigStmt (Just e) s stmt (Just e) s
  BigSkip : BigStmt e s Skip e s
  BigAIns : BigAExpr s e i -> BigStmt Nothing s (Assign x e) Nothing (Insert {x} i s p)
  BigAUp : BigAExpr s e i -> EnvUpdate {x} p s i s' -> BigStmt Nothing s (Assign x e) Nothing s'
  BigSeq : BigStmt e s stmt e' s' -> BigStmt e' s' stmt' e'' s'' -> BigStmt e s (Seq stmt stmt') e'' s''
  BigIfT : BigBExpr s b True -> BigStmt Nothing s stmt e s' -> BigStmt Nothing s (If b stmt stmt') e s'
  BigIfF : BigBExpr s b False -> BigStmt Nothing s stmt' e s' -> BigStmt Nothing s (If b stmt stmt') e s'
  BigWhileT : BigBExpr s b True -> BigStmt Nothing s stmt e s' -> BigStmt e s' (While b stmt) e' s'' -> BigStmt Nothing s (While b stmt) e' s''
  BigWhileF : BigBExpr s b False -> BigStmt Nothing s (While b stmt) Nothing s
  BigThrow : BigAExpr s e i -> BigStmt Nothing s (Throw e) (Just i) s
  BigTryYes : BigStmt Nothing s stmt Nothing s' -> BigStmt Nothing s (TryCatch stmt v stmt') Nothing s'
  BigTryNoIns : BigStmt Nothing s stmt (Just e) s' -> BigStmt Nothing (Insert {x} e s' p) stmt' e' s'' -> BigStmt Nothing s (TryCatch stmt x stmt') e' s''
  BigTryNoUp : BigStmt Nothing s stmt (Just e) s' -> EnvUpdate {x} p s' e s'' -> BigStmt Nothing s'' stmt' e' s''' -> BigStmt Nothing s (TryCatch stmt x stmt') e' s'''
