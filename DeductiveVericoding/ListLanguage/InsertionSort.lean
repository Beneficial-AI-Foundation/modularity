import Mathlib.Data.List.Perm.Basic
import DeductiveVericoding.ListLanguage.Basic

open ListLanguage

def insertVal (a : Nat) : List Nat → List Nat
  | [] => [a]
  | h :: t => if a ≤ h then a :: h :: t else h :: insertVal a t

def Ordered : List Nat → Prop
  | [] => True
  | [_] => True
  | x :: y :: xs => x ≤ y ∧ Ordered (y :: xs)

/-- The sorting invariant: output is sorted and a permutation of input -/
def Sorted (inp out : List Nat) : Prop :=
  Ordered out ∧ List.Perm inp out

/-! ## Properties of insertVal -/

theorem insertVal_sorted (a : Nat) (l : List Nat) (hs : Ordered l) :
    Ordered (insertVal a l) := by
  induction l with
  | nil => trivial
  | cons x xs ih =>
    simp only [insertVal]; split_ifs with h <;> [exact ⟨h, hs⟩; skip]
    cases xs with
    | nil => simp_all [insertVal, Ordered]; omega
    | cons y ys =>
      simp only [Ordered, insertVal] at hs ⊢; split_ifs with h'
      all_goals simp_all [insertVal, Ordered]; try omega

theorem insertVal_perm (a : Nat) (l : List Nat) :
    List.Perm (a :: l) (insertVal a l) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [insertVal]; split_ifs <;> [rfl; exact (List.Perm.swap x a xs).trans (.cons x ih)]

/-- All elements in a sorted list are ≥ its head -/
theorem Ordered.all_ge_head (h : Nat) (t : List Nat) (hs : Ordered (h :: t)) :
    ∀ x ∈ t, h ≤ x := by
  intro x hx
  induction t generalizing h with
  | nil => nomatch hx
  | cons h' t' ih =>
    cases List.mem_cons.mp hx with
    | inl heq => rw [heq]; exact hs.1
    | inr hmem =>
      have hh' : h ≤ h' := hs.1
      have ht'_ord : Ordered (h' :: t') := hs.2
      exact Nat.le_trans hh' (ih h' ht'_ord hmem)

/-- For sorted h :: t and a ≤ h, insertVal a t = a :: t -/
theorem insertVal_le_cons (a h : Nat) (t : List Nat) (hs : Ordered (h :: t)) (hle : a ≤ h) :
    insertVal a t = a :: t := by
  cases t with
  | nil => rfl
  | cons h' t' =>
    simp only [insertVal]
    have hh' : h ≤ h' := hs.1
    have hah' : a ≤ h' := Nat.le_trans hle hh'
    simp [hah']
