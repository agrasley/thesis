module V where

import qualified Data.Map.Strict as M

import Dim

data V a = One a
         | Chc (M.Map a Dim)
  deriving (Show,Eq)

instance Functor V where
  fmap f (One a) = One (f a)
  fmap f (Chc m) = if M.size m' == 1 then
                     One . head . M.keys $ m'
                   else
                     Chc m'
    where m' = M.mapKeysWith DOr f m
