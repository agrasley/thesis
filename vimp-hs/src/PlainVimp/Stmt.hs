module PlainVimp.Stmt where

import Control.Monad.State
import Control.Monad (when)
import qualified Data.Map.Strict as M

import PlainVimp.Expr


data Stmt =
    Skip
  | Assign VName AExpr
  | Seq Stmt Stmt
  | If BExpr Stmt Stmt
  | While BExpr Stmt
  deriving (Eq,Show)

seval :: (MonadState (M.Map VName Int) m) => Stmt -> m ()
seval Skip = return ()
seval (Assign v a) = do
  s <- get
  a' <- aeval a
  put (M.insert v a' s)
seval (Seq s1 s2) = seval s1 >> seval s2
seval (If c t e) = do
  c' <- beval c
  if c' then
    seval t
  else
    seval e
seval (While c s) = do
  c' <- beval c
  when c'
    (seval s)
