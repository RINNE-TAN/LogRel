

import LogRel.STLC.Basic
import LogRel.STLC.OpenClose
inductive value : Expr → Prop where
  | lam : ∀ e, value (.lam e)
  | unit : value .unit

abbrev Ctx :=
  Expr → Expr

notation:max a "⟦" b "⟧" => a b

inductive ctx𝔹 : Ctx → Prop where
  | appl : ∀ arg, ctx𝔹 (fun X => .app X arg)
  | appr : ∀ v, value v → ctx𝔹 (fun X => .app v X)

inductive ctx𝕄 : Ctx → Prop where
  | hole : ctx𝕄 id
  | cons𝔹 : ∀ B M, ctx𝔹 B → ctx𝕄 M → ctx𝕄 (B ∘ M)

inductive head : Expr → Expr → Prop where
  | app : ∀ e v, value v → head (.app (.lam e) v) (opening 0 v e)

inductive step : Expr → Expr → Prop where
  | step𝕄 : ∀ M e₀ e₁, ctx𝕄 M → head e₀ e₁ → step M⟦e₀⟧ M⟦e₁⟧

inductive stepn : Expr → Expr → Prop
  | refl : ∀ e, stepn e e
  | multi : ∀ e₁ e₂ e₃, step e₁ e₂ → stepn e₂ e₃ → stepn e₁ e₃

theorem step_appl : ∀ e₀ e₁ arg, step e₀ e₁ → step (.app e₀ arg) (.app e₁ arg) :=
  by
  intros e₀ e₁ arg Hstep
  cases Hstep
  case step𝕄 M e₀ e₁ HM Hhead =>
    apply step.step𝕄 (fun X => .app (M X) arg)
    apply ctx𝕄.cons𝔹 (fun X => .app X arg)
    apply ctx𝔹.appl; apply HM; apply Hhead

theorem step_appr : ∀ e₀ e₁ v, step e₀ e₁ → value v → step (.app v e₀) (.app v e₁) :=
  by
  intros e₀ e₁ v Hstep Hvalue
  cases Hstep
  case step𝕄 M e₀ e₁ HM Hhead =>
    apply step.step𝕄 (fun X => .app v (M X))
    apply ctx𝕄.cons𝔹 (fun X => .app v X)
    apply ctx𝔹.appr; apply Hvalue; apply HM; apply Hhead

theorem stepn_appr : ∀ e₀ e₁ v, stepn e₀ e₁ → value v → stepn (.app v e₀) (.app v e₁) :=
  by
  intros e₀ e₁ v Hstep Hvalue
  induction Hstep
  case refl => apply stepn.refl
  case multi Hstep _ IH =>
    apply stepn.multi
    apply step_appr; apply Hstep; apply Hvalue
    apply IH

theorem stepn_trans : ∀ e₁ e₂ e₃, stepn e₁ e₂ → stepn e₂ e₃ → stepn e₁ e₃ :=
  by
  intros e₀ e₁ e₃ H₁ H₂
  induction H₁
  case refl => apply H₂
  case multi H₃ _ IH =>
    apply stepn.multi
    apply H₃; apply IH; apply H₂
