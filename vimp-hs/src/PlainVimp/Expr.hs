module PlainVimp.Expr where

import Control.Monad.State
import qualified Data.Map.Strict as M
import Data.Maybe

type VName = String

data AExpr =
    N Int
  | V VName
  | Plus AExpr AExpr
  deriving (Eq,Show)

aeval :: (MonadState (M.Map VName Int) m) => AExpr -> m Int
aeval (N i) = return i
aeval (V v) = do
  s <- get
  return . fromJust . M.lookup v $ s
aeval (Plus l r) = (+) <$> aeval l <*> aeval r

data BExpr =
    Bc Bool
  | Not BExpr
  | And BExpr BExpr
  | Less AExpr AExpr
  deriving (Eq,Show)

beval :: (MonadState (M.Map VName Int) m) => BExpr -> m Bool
beval (Bc b) = return b
beval (Not e) = not <$> beval e
beval (And l r) = (&&) <$> beval l <*> beval r
beval (Less l r) = (<) <$> aeval l <*> aeval r
