

import LogRel.STLC.SmallStep
import LogRel.STLC.Typing
@[simp]
def halts (e : Expr) :=
  ∃ v, value v ∧ stepn e v

@[simp]
def SN : Expr → Ty → Prop
  | e, .unit => halts e
  | f, .arrow τ𝕒 τ𝕓 => halts f ∧ ∀ arg, SN arg τ𝕒 → SN (.app f arg) τ𝕓

theorem SN_impl_halts : ∀ e τ, SN e τ → halts e := by
  intros e τ HSN
  induction τ
  case unit => apply HSN
  case arrow => apply HSN.left

theorem halts_reduction : ∀ e₀ e₁, step e₀ e₁ → (halts e₀ ↔ halts e₁) :=
  by
  intros e₀ e₁ Hstep
  constructor
  . admit
  . admit

theorem SN_reduction : ∀ e₀ e₁ τ, step e₀ e₁ → (SN e₀ τ ↔ SN e₁ τ) :=
  by
  intros e₀ e₁ τ Hstep
  constructor
  . intros HSN₀
    induction τ generalizing e₀ e₁
    case unit =>
      apply (halts_reduction _ _ _).mp
      apply HSN₀; apply Hstep
    case arrow IHa IHb =>
      constructor
      . apply (halts_reduction _ _ _).mp
        apply HSN₀.left; apply Hstep
      . intro arg HSN₁
        apply IHb
        apply step_appl; apply Hstep
        apply HSN₀.right; apply HSN₁
  . intros HSN₀
    induction τ generalizing e₀ e₁
    case unit =>
      apply (halts_reduction _ _ _).mpr
      apply HSN₀; apply Hstep
    case arrow IHa IHb =>
      constructor
      . apply (halts_reduction _ _ _).mpr
        apply HSN₀.left; apply Hstep
      . intro arg HSN₁
        apply IHb
        apply step_appl; apply Hstep
        apply HSN₀.right; apply HSN₁

abbrev Subst :=
  List Expr

@[simp]
def SN_Env : Subst → TEnv → Prop
  | [], [] => true
  | v :: vs, τ :: τs => SN v τ ∧ SN_Env vs τs
  | _, _ => false

@[simp]
def substs : Subst → Expr → Expr
  | [], e => e
  | γ :: γs, e => substs γs (subst γs.length γ e)

theorem typing_impl_SN : ∀ Γ e τ γs, typing Γ e τ → SN_Env γs Γ → SN (substs γs e) τ :=
  by
  intros Γ e τ γs Hτ HSNΓ
  induction Hτ generalizing γs
  case fvar => admit
  case lam => admit
  case app => admit
  case unit => admit

theorem normalization : ∀ e τ, typing [] e τ → halts e := by admit
