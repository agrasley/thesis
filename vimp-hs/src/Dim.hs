module Dim where

import qualified Data.Text as T

type Var = T.Text

data Dim = DLit Bool
         | DRef Var
         | DNot Dim
         | DAnd Dim Dim
         | DOr  Dim Dim
  deriving (Show,Eq)
