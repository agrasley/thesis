module Sat

import Dim
import Data.SortedSet
import Debug.Error
import Env
import Data.List

%include C "sat.h"
%include C "sat.o"

%language ElabReflection
%access public export

dimGetVars' : Dim -> SortedSet DimVar -> SortedSet DimVar
dimGetVars' (DLit _) s = s
dimGetVars' (DRef v) s = insert v s
dimGetVars' (DNot d) s = dimGetVars' d s
dimGetVars' (DAnd l r) s = dimGetVars' r (dimGetVars' l s)
dimGetVars' (DOr l r) s = dimGetVars' r (dimGetVars' l s)

dimGetVars : Dim -> SortedSet DimVar
dimGetVars d = dimGetVars' d empty

varsToStr : SortedSet DimVar -> String
varsToStr = foldr (\v, s => s ++ "(declare-const " ++ v ++ " Bool)\n") ""

dimToStr' : Dim -> String
dimToStr' (DLit True) = "true"
dimToStr' (DLit False) = "false"
dimToStr' (DRef v) = v
dimToStr' (DNot d) = "(not " ++ dimToStr' d ++ ")"
dimToStr' (DAnd l r) = "(and " ++ dimToStr' l ++ " " ++ dimToStr' r ++ ")"
dimToStr' (DOr l r) = "(or " ++ dimToStr' l ++ " " ++ dimToStr' r ++ ")"

dimToStr : Dim -> String
dimToStr d = vars ++ "(assert " ++ dimToStr' d ++ ")\n(check-sat)"
  where
    vars = varsToStr . dimGetVars $ d

writeFile : Dim -> IO (Either FileError ())
writeFile d = do
  f' <- openFile "in.smt2" WriteTruncate
  case f' of
    (Left e) => pure (Left e)
    (Right f) => do
      g' <- fPutStr f (dimToStr d)
      case g' of
        (Left e) => pure (Left e)
        (Right ()) => do
          closeFile f
          pure (Right ())

callSat : IO Int
callSat = foreign FFI_C "runsat" (() -> IO Int) ()

data SATError = SatE | FileE (FileError)

satIO : Dim -> IO (Either SATError Bool)
satIO d = do
  res <- writeFile d
  case res of
    (Left e) => pure (Left (FileE e))
    (Right ()) => do
      i <- callSat
      case i of
        0 => pure (Right False)
        1 => pure (Right True)
        _ => pure (Left SatE)

sat : Dim -> Bool
sat d = case unsafePerformIO (satIO d) of
  (Left SatE) => error "Error with the SAT solver"
  (Left (FileE _)) => error "Error writing smt2 file"
  (Right b) => b

unsat : Dim -> Bool
unsat = not . sat

taut : Dim -> Bool
taut = unsat . DNot

imp : Dim -> Dim -> Dim
imp x y = DOr (DNot x) y

xor : Dim -> Dim -> Dim
xor x y = DAnd (DOr x y) (DNot (DAnd x y))

equ : Dim -> Dim -> Dim
equ x y = DNot (xor x y)

equiv : Dim -> Dim -> Bool
equiv x y = taut (equ x y)

implies : Dim -> Dim -> Bool
implies x y = taut (imp x y)

-- Type level sat

SatEnv : List DimVar -> Type
SatEnv xs = Env xs Bool

data Sat : SatEnv xs -> Dim -> Type where
  SatT : Sat env (DLit True)
  SatR : EnvLookup {x} p env True -> Sat env (DRef x)
  SatN : Not (Sat env d) -> Sat env (DNot d)
  SatA : Sat env l -> Sat env r -> Sat env (DAnd l r)
  SatOL : Sat env l -> Sat env (DOr l r)
  SatOR : Sat env r -> Sat env (DOr l r)

data Unsat : Dim -> Type where
  MkUnsat : DimHasVar x d ->
            EnvLookup {x} p env True ->
            Not (Sat env d) ->
            EnvLookup {x} p' env' False ->
            Not (Sat env' d) ->
            Unsat d

data Taut : Dim -> Type where
  MkTaut : Unsat (DNot d) -> Taut d

data Implies : Dim -> Dim -> Type where
  MkImplies : Taut (imp x y) -> Implies x y
