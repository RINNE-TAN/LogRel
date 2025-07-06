

import LogRel.STLC.Basic
import LogRel.STLC.OpenClose
inductive value : Expr → Prop where
  | lam : ∀ e, value (.lam e)
  | unit : value .unit

abbrev Ctx :=
  Expr → Expr

notation:max a "⟦" b "⟧" => a b

inductive ctx𝔹 : Ctx → Prop where
  | appl : ∀ arg, lc arg → ctx𝔹 (fun X => .app X arg)
  | appr : ∀ v, value v → ctx𝔹 (fun X => .app v X)

inductive ctx𝕄 : Ctx → Prop where
  | hole : ctx𝕄 id
  | cons𝔹 : ∀ B M, ctx𝔹 B → ctx𝕄 M → ctx𝕄 (B ∘ M)

inductive head : Expr → Expr → Prop where
  | app₁ : ∀ e v, value v → head (.app (.lam e) v) (opening 0 v e)

inductive step : Expr → Expr → Prop where
  | step𝕄 : ∀ M e₀ e₁, ctx𝕄 M → head e₀ e₁ → step M⟦e₀⟧ M⟦e₁⟧

inductive stepn : Expr → Expr → Prop
  | refl : ∀ e, stepn e e
  | trans : ∀ e₁ e₂ e₃, stepn e₁ e₂ → step e₂ e₃ → stepn e₁ e₃
