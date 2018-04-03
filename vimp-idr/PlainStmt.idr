module PlainStmt

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

data BigStmt : State xs -> Stmt -> State xs' -> Type where
  BigSkip : BigStmt s Skip s
  BigAIns : BigAExpr s e i -> BigStmt s (Assign x e) (Insert {x} i s p)
  BigAUp : BigAExpr s e i -> EnvUpdate {x} p s i s' -> BigStmt s (Assign x e) s'
  BigSeq : BigStmt s stmt s' -> BigStmt s' stmt' s'' -> BigStmt s (Seq stmt stmt') s''
  BigIfT : BigBExpr s b True -> BigStmt s stmt s' -> BigStmt s (If b stmt stmt') s'
  BigIfF : BigBExpr s b False -> BigStmt s stmt' s' -> BigStmt s (If b stmt stmt') s'
  BigWhileT : BigBExpr s b True -> BigStmt s stmt s' -> BigStmt s' (While b stmt) s'' -> BigStmt s (While b stmt) s''
  BigWhileF : BigBExpr s b False -> BigStmt s (While b stmt) s
