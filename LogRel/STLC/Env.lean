

import Mathlib.Data.Nat.Basic
@[simp]
def getr {α : Type} (x : ℕ) (l : List α) : Option α :=
  match l with
  | [] => none
  | head :: tails => if tails.length == x then some head else getr x tails

@[simp]
def binds {α : Type} (x : ℕ) (a : α) (l : List α) :=
  getr x l = some a
