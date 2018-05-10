module NewSat

import NewDim
import Env
import Data.SortedSet
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

data SSElem : a -> SortedSet a -> Type where
  MkSSElem : Elem x (Data.SortedSet.toList ss) -> SSElem x ss

data ResResult : Type where
  ResT : ResResult
  ResEnv : SortedSet DimVar -> SortedSet DimVar -> ResResult

data Resolution : List Clause -> ResResult -> Type where
  ResStartT : SSElem True z -> Resolution [DOr x y z] ResT
  ResStartE : Resolution [DOr x y z] (ResEnv x y)
  ResTrue : Resolution xs res -> SSElem True z -> Resolution ((DOr x y z)::xs) res
  ResNextT : Resolution xs ResT -> Resolution ((DOr x y z)::xs) (ResEnv x y)
  ResNextE : Resolution xs (ResEnv a b) -> Resolution ((DOr x y z)::xs) (ResEnv (difference a y) (difference b x))

data SSNonEmpty : SortedSet a -> Type where
  MkSSNonEmpty : NonEmpty (Data.SortedSet.toList ss) -> SSNonEmpty ss

data Sat : Dim -> Type where
  SatT : Resolution xs ResT -> Sat (DAnd xs)
  SatE1 : SSNonEmpty x -> Resolution xs (ResEnv x y) -> Sat (DAnd xs)
  SatE2 : SSNonEmpty y -> Resolution xs (ResEnv x y) -> Sat (DAnd xs)

Unsat : Dim -> Type
Unsat d = Not (Sat d)
