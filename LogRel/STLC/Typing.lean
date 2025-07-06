

import LogRel.STLC.Basic
import LogRel.STLC.OpenClose
@[simp]
def getr {α : Type} (x : ℕ) (l : List α) : Option α :=
  match l with
  | [] => none
  | head :: tails => if tails.length == x then some head else getr x tails

@[simp]
def binds {α : Type} (x : ℕ) (a : α) (l : List α) :=
  getr x l = some a

abbrev TEnv :=
  List Ty

inductive typing : TEnv → Expr → Ty → Prop where
  | fvar : ∀ Γ x τ, binds x τ Γ → typing Γ (.fvar x) τ
  | lam : ∀ Γ e τ𝕒 τ𝕓, typing (τ𝕒 :: Γ) (opening 0 (.fvar Γ.length) e) τ𝕓 → typing Γ (.lam e) (.arrow τ𝕒 τ𝕓)
  | app : ∀ Γ f arg τ𝕒 τ𝕓, typing Γ f (.arrow τ𝕒 τ𝕓) → typing Γ arg τ𝕒 → typing Γ (.app f arg) τ𝕓
  | unit : ∀ Γ, typing Γ .unit .unit
