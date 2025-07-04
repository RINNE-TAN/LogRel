

import Mathlib.Data.Nat.Basic
inductive Ty : Type where
  | unit
  | arrow (τ𝕒 : Ty) (τ𝕓 : Ty)

inductive Expr : Type where
  | bvar (i : ℕ)
  | fvar (x : ℕ)
  | lam (e : Expr)
  | app (f : Expr) (arg : Expr)
  | unit
