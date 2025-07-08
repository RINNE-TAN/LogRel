

import Mathlib.Data.Nat.Basic
@[simp]
def getr {α : Type} (x : ℕ) (l : List α) : Option α :=
  match l with
  | [] => none
  | head :: tails => if tails.length == x then some head else getr x tails

@[simp]
def binds {α : Type} (x : ℕ) (a : α) (l : List α) :=
  getr x l = some a

theorem getr_none {α : Type} : ∀ x (l : List α), x ≥ l.length → getr x l = none :=
  by
  intros x l HGe
  induction l
  case nil => rfl
  case cons tail IH =>
    simp at HGe
    by_cases HEq : tail.length = x
    . omega
    . simp [if_neg HEq]; apply IH; omega
