module V


-- Variational Imp Expressions

data Dim : Type where
DLit : Bool -> Dim
DRef : String -> Dim
DNot : Dim -> Dim
DAnd : Dim -> Dim -> Dim
DOr  : Dim -> Dim -> Dim

VCtx : Type
VCtx = Dim

data V : Type -> Type where
One : a -> V a
Chc : Dim -> V a -> V a -> V a

data AExprV : Type where
NV : V Int -> AExprV
VarV : V String -> AExprV
AddV : V AExprV -> V AExprV -> AExprV

data BExprV : Type where
BV : V Bool -> BExprV
NotV : V BExprV -> BExprV
AndV : V BExprV -> V BExprV -> BExprV
LessV : V AExprV -> V AExprV -> BExprV

VState : Type
VState = List (String,V (Maybe Int))

--data SSAExpr : (VCtx,State,AExpr) -> (VCtx,State,AExpr) -> Type where
--  AddOne : SSAExpr (v,s,Add (One (N (One ))))

-- Testing
