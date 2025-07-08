

import Mathlib.Data.Set.Insert
import LogRel.STLC.Basic
import LogRel.STLC.Env
@[simp]
def closedb_at (e : Expr) (i : ℕ) : Prop :=
  match e with
  | .bvar x => x < i
  | .fvar _ => true
  | .lam e => closedb_at e (i + 1)
  | .app f arg => closedb_at f i ∧ closedb_at arg i
  | .unit => true

@[simp]
def lc e :=
  closedb_at e 0

@[simp]
def opening (i : ℕ) (v : Expr) : Expr → Expr
  | .bvar j => if j = i then v else .bvar j
  | .fvar x => .fvar x
  | .lam e => .lam (opening (i + 1) v e)
  | .app f arg => .app (opening i v f) (opening i v arg)
  | .unit => .unit

@[simp]
def subst (x : ℕ) (v : Expr) : Expr -> Expr
  | .bvar i => .bvar i
  | .fvar y => if x = y then v else .fvar y
  | .lam e => .lam (subst x v e)
  | .app f arg => .app (subst x v f) (subst x v arg)
  | .unit => .unit

abbrev Subst :=
  List Expr

@[simp]
def substs (γs : Subst) : Expr -> Expr
  | .bvar i => .bvar i
  | .fvar y => (getr y γs).elim (.fvar y) id
  | .lam e => .lam (substs γs e)
  | .app f arg => .app (substs γs f) (substs γs arg)
  | .unit => .unit

@[simp]
def fv : Expr → Set ℕ
  | .bvar _ => ∅
  | .fvar x => { x }
  | .lam e => fv e
  | .app f arg => fv f ∪ fv arg
  | .unit => ∅

theorem subst_intro : ∀ x e v i, x ∉ fv e → subst x v (opening i (.fvar x) e) = opening i v e :=
  by
  intros x e _ i HFv
  induction e generalizing i with
  | bvar j =>
    by_cases HEq : j = i
    . simp [HEq]
    . simp [if_neg HEq]
  | fvar y =>
    simp; intro HEq
    rw [HEq] at HFv
    nomatch HFv
  | lam _ IH => simp; apply IH; apply HFv
  | app _ _ IH₀ IH₁ =>
    simp; simp at HFv; constructor
    apply IH₀; apply HFv.left
    apply IH₁; apply HFv.right
  | unit => simp

theorem substs_empty : ∀ e, substs [] e = e := by
  intro e
  induction e
  case bvar => rfl
  case fvar => rfl
  case lam IH => simp; apply IH
  case app IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply IH₁
  case unit => rfl
