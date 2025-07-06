

import LogRel.STLC.SmallStep
import LogRel.STLC.Typing
@[simp]
def normalizable (e : Expr) :=
  ∃ v, value v ∧ stepn e v

@[simp]
def SN : Expr → Ty → Prop
  | e, .unit => normalizable e
  | f, .arrow τ𝕒 τ𝕓 => normalizable f ∧ ∀ arg, SN arg τ𝕒 → SN (.app f arg) τ𝕓

theorem SN_impl_normalizable : ∀ e τ, SN e τ → normalizable e :=
  by
  intros e τ HSN
  induction τ
  case unit => apply HSN
  case arrow => apply HSN.left

theorem SN_reduction : ∀ e₀ e₁ τ, typing [] e₀ τ → step e₀ e₁ → (SN e₀ τ ↔ SN e₁ τ) := by
  intros e₀ e₁ τ Hτ Hstep
  cases Hstep
  case step𝕄 HM Hhead =>
    induction HM generalizing τ
    case hole => admit
    case cons𝔹 HB HM IH =>
      cases HB
      case appl => admit
      case appr => admit

example : ∀ e τ, typing [] e τ → SN e τ := by
  generalize HEqΓ : [] = Γ
  intros e τ Hτ
  induction Hτ
  case fvar Hbinds =>
    rw [← HEqΓ] at Hbinds
    nomatch Hbinds
  case lam e _ _ _ IH =>
    constructor
    . exists .lam e
      constructor
      . apply value.lam
      . apply stepn.refl
    . admit
  case app IHf IHarg =>
    apply (IHf HEqΓ).right
    apply (IHarg HEqΓ)
  case unit =>
    exists .unit
    constructor
    . apply value.unit
    . apply stepn.refl

theorem strong_normalization : ∀ e τ, typing [] e τ → normalizable e := by admit
