

import LogRel.STLC.SmallStep
import LogRel.STLC.Typing
@[simp]
def halts (e : Expr) :=
  ∃ v, value v ∧ stepn e v

@[simp]
def SN : Expr → Ty → Prop
  | e, .unit => closed e ∧ lc e ∧ halts e
  | f, .arrow τ𝕒 τ𝕓 => closed f ∧ lc f ∧ halts f ∧ ∀ arg, SN arg τ𝕒 → SN (.app f arg) τ𝕓

theorem SN_impl_halts : ∀ e τ, SN e τ → halts e := by
  intros e τ HSN
  induction τ
  case unit => apply HSN.right.right
  case arrow => apply HSN.right.right.left

theorem closed_step : ∀ e₀ e₁, step e₀ e₁ → (closed e₀ ↔ closed e₁) :=
  by
  intros e₀ e₁ Hstep
  constructor
  . admit
  . admit

theorem lc_step : ∀ e₀ e₁, step e₀ e₁ → (lc e₀ ↔ lc e₁) :=
  by
  intros e₀ e₁ Hstep
  constructor
  . admit
  . admit

theorem halts_step : ∀ e₀ e₁, step e₀ e₁ → (halts e₀ ↔ halts e₁) :=
  by
  intros e₀ e₁ Hstep
  constructor
  . admit -- need determinstic
  . intro Hhalts
    have ⟨v, Hvalue, Hstepn⟩ := Hhalts
    exists v; constructor; apply Hvalue
    apply stepn.multi; apply Hstep; apply Hstepn

theorem SN_step : ∀ e₀ e₁ τ, step e₀ e₁ → (SN e₀ τ ↔ SN e₁ τ) :=
  by
  intros e₀ e₁ τ Hstep
  constructor
  . intros HSN₀
    induction τ generalizing e₀ e₁
    case unit =>
      have ⟨Hclosed, Hlc, Hhalts⟩ := HSN₀
      constructor
      . apply (closed_step _ _ _).mp
        apply Hclosed; apply Hstep
      constructor
      . apply (lc_step _ _ _).mp
        apply Hlc; apply Hstep
      . apply (halts_step _ _ _).mp
        apply Hhalts; apply Hstep
    case arrow IHa IHb =>
      have ⟨Hclosed, Hlc, Hhalts, IH⟩ := HSN₀
      constructor
      . apply (closed_step _ _ _).mp
        apply Hclosed; apply Hstep
      constructor
      . apply (lc_step _ _ _).mp
        apply Hlc; apply Hstep
      constructor
      . apply (halts_step _ _ _).mp
        apply Hhalts; apply Hstep
      . intro arg HSN₁
        apply IHb
        apply step_appl; apply Hstep
        apply IH; apply HSN₁
  . intros HSN₀
    induction τ generalizing e₀ e₁
    case unit =>
      have ⟨Hclosed, Hlc, Hhalts⟩ := HSN₀
      constructor
      . apply (closed_step _ _ _).mpr
        apply Hclosed; apply Hstep
      constructor
      . apply (lc_step _ _ _).mpr
        apply Hlc; apply Hstep
      . apply (halts_step _ _ _).mpr
        apply Hhalts; apply Hstep
    case arrow IHa IHb =>
      have ⟨Hclosed, Hlc, Hhalts, IH⟩ := HSN₀
      constructor
      . apply (closed_step _ _ _).mpr
        apply Hclosed; apply Hstep
      constructor
      . apply (lc_step _ _ _).mpr
        apply Hlc; apply Hstep
      constructor
      . apply (halts_step _ _ _).mpr
        apply Hhalts; apply Hstep
      . intro arg HSN₁
        apply IHb
        apply step_appl; apply Hstep
        apply IH; apply HSN₁

theorem SN_stepn : ∀ e₀ e₁ τ, stepn e₀ e₁ → (SN e₀ τ ↔ SN e₁ τ) :=
  by
  intros e₀ e₁ τ Hstepn
  induction Hstepn
  case refl => rfl
  case multi Hstep _ IH => rw [← IH]; apply SN_step; apply Hstep

inductive SN_Env : Subst → TEnv → Prop
  | nil : SN_Env [] []
  | cons : ∀ γ γs τ τs, SN γ τ → SN_Env γs τs → SN_Env (γ :: γs) (τ :: τs)

theorem SN_Env_impl_length_eq : ∀ γs τs, SN_Env γs τs → γs.length = τs.length :=
  by
  intros γs τs HSNΓ
  induction HSNΓ
  case nil => rfl
  case cons IH => simp; apply IH

theorem fundamental : ∀ Γ e τ γs, typing Γ e τ → SN_Env γs Γ → SN (substs γs e) τ :=
  by
  intros Γ e τ γs Hτ HSNΓ
  induction Hτ generalizing γs
  case fvar Γ x _ Hbinds =>
    induction HSNΓ
    case nil => nomatch Hbinds
    case cons γ γs τ τs HSN HSNΓ IH =>
      simp; simp at Hbinds
      rw [SN_Env_impl_length_eq _ _ HSNΓ]
      by_cases HEq : (τs.length = x)
      . simp [if_pos HEq]
        simp [if_pos HEq] at Hbinds
        rw [← Hbinds]; apply HSN
      . simp [if_neg HEq]
        simp [if_neg HEq] at Hbinds
        apply IH; apply Hbinds
  case lam e _ _ _ HFv IH =>
    constructor
    . admit
    constructor
    . admit
    constructor
    . exists substs γs (.lam e)
      constructor
      . constructor
      . apply stepn.refl
    . intro arg HSN
      have ⟨v, Hvalue, Hstepn⟩ := SN_impl_halts _ _ HSN
      apply (SN_stepn _ _ _ _).mpr; apply IH (v :: γs); apply SN_Env.cons
      apply (SN_stepn _ _ _ _).mp; apply HSN; apply Hstepn; apply HSNΓ
      apply stepn_trans; apply stepn_appr; apply Hstepn; constructor
      apply stepn.multi; apply step.step𝕄 id; apply ctx𝕄.hole; apply head.app; apply Hvalue
      rw [← SN_Env_impl_length_eq _ _ HSNΓ, ← subst_intro γs.length, ← substs_opening_comm]
      all_goals admit
  case app IH₀ IH₁ =>
    apply (IH₀ _ HSNΓ).right.right.right
    apply IH₁ _ HSNΓ
  case unit =>
    constructor
    . simp
    constructor
    . constructor
    . exists .unit
      constructor
      . constructor
      . apply stepn.refl

theorem normalization : ∀ e τ, typing [] e τ → halts e :=
  by
  intros e τ Hτ
  apply SN_impl_halts; rw [← substs_empty e]
  apply fundamental; apply Hτ; apply SN_Env.nil
