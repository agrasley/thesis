module Env

import Data.List

%access public export

data Env : List String -> Type -> Type where
  Empty : Env [] a
  Insert : a -> Env xs a -> Not (Elem x xs) -> Env (x::xs) a

envLookup : Elem x xs -> Env xs a -> a
envLookup Here (Insert a _ _) = a
envLookup (There el) (Insert a as _) = envLookup el as

data EnvLookup : Elem x xs -> Env xs a -> a -> Type where
  Here : EnvLookup Here (Insert a as p) a
  There : EnvLookup el env a -> EnvLookup (There el) (Insert a' env p) a

envUpdate : Elem x xs -> Env xs a -> a -> Env xs a
envUpdate Here (Insert a env p) a' = Insert a' env p
envUpdate (There el) (Insert a env p) a' = Insert a (envUpdate el env a') p

data EnvUpdate : Elem x xs -> Env xs a -> a -> Env xs a -> Type where
  UpHere : EnvUpdate Here (Insert a env p) a' (Insert a' env p)
  UpThere : EnvUpdate el env a env' -> EnvUpdate (There el) (Insert a' env p) a (Insert a' env' p')

envExtend : Either (Not (Elem x xs)) (Elem x xs) -> Env xs a -> a -> Either (Env (x::xs) a) (Env xs a)
envExtend (Left p) env a = Left (Insert a env p)
envExtend (Right p) env a = Right (envUpdate p env a)

data EnvExtend : Either (Not (Elem x xs)) (Elem x xs) -> Env xs a -> a -> Either (Env (x::xs) a) (Env xs a) -> Type where
  ExLeft : EnvExtend (Left p) env a (Left (Insert a env p))
  ExRight : EnvUpdate p env a env' -> EnvExtend (Right p) env a (Right env')
