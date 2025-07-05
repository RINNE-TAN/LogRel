

import LogRel.SmallStep
import LogRel.Typing
def termination (e : Expr) :=
  ∃ v, value v ∧ stepn e v

theorem strong_normalization : ∀ Γ e τ, typing Γ e τ → termination e := by admit
