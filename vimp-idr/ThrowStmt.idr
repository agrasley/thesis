module ThrowStmt

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

ErrCode : Type
ErrCode = Int

data BigStmt : Either ErrCode (State xs) -> Stmt -> Either ErrCode (State xs') -> Type where
  BigErr : BigStmt (Left i) stmt (Left i)
  BigSkip : BigStmt s Skip s
  BigAIns : BigAExpr s e i -> BigStmt (Right s) (Assign x e) (Right (Insert {x} i s p))
  BigAUp : BigAExpr s e i -> EnvUpdate {x} p s i s' -> BigStmt (Right s) (Assign x e) (Right s')
  BigSeq : BigStmt s stmt s' -> BigStmt s' stmt' s'' -> BigStmt s (Seq stmt stmt') s''
  BigIfT : BigBExpr s b True -> BigStmt (Right s) stmt s' -> BigStmt (Right s) (If b stmt stmt') s'
  BigIfF : BigBExpr s b False -> BigStmt (Right s) stmt' s' -> BigStmt (Right s) (If b stmt stmt') s'
  BigWhileT : BigBExpr s b True -> BigStmt (Right s) stmt s' -> BigStmt s' (While b stmt) s'' -> BigStmt (Right s) (While b stmt) s''
  BigWhileF : BigBExpr s b False -> BigStmt (Right s) (While b stmt) (Right s)
  BigThrow : BigAExpr s e i -> BigStmt (Right s) (Throw e) (Left i)
