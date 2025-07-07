

import LogRel.STLC.Basic
@[simp]
def opening (i : ℕ) (v : Expr) : Expr → Expr
  | .bvar j => if j = i then v else .bvar j
  | .fvar x => .fvar x
  | .lam e => .lam (opening (i + 1) v e)
  | .app f arg => .app (opening i v f) (opening i v arg)
  | .unit => .unit

@[simp]
def closedb_at (e : Expr) (i : ℕ) : Prop :=
  match e with
  | .bvar x => x < i
  | .fvar _ => true
  | .lam e => closedb_at e (i + 1)
  | .app f arg => closedb_at f i ∧ closedb_at arg i
  | .unit => true

@[simp]
def subst (x : ℕ) (v : Expr) : Expr -> Expr
  | .bvar i => .bvar i
  | .fvar y => if x = y then v else .fvar y
  | .lam e => .lam (subst x v e)
  | .app f arg => .app (subst x v f) (subst x v arg)
  | .unit => .unit

@[simp]
def lc e :=
  closedb_at e 0
