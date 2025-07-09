import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

open Nat
open Finset

def sum_spec (n: ℕ) : Prop :=
  2 * (range (n + 1)).sum id = n * (n + 1)

lemma base_proof : sum_spec 0 := by
  unfold sum_spec; simp

lemma ind_proof (n : ℕ) (ih : sum_spec n) : sum_spec (n+1) := by
  unfold sum_spec; rw [sum_range_succ, mul_add, ih]
  unfold id; ring

theorem sum_proof (n : ℕ) : sum_spec n := by
  induction n with
  | zero => exact base_proof
  | succ n ih => exact ind_proof n ih

#print sum_proof

#print Nat.recAux

def Nat.recAux2.{u} : {motive : ℕ → Sort u} →
    motive 0 →
    ((n : ℕ) → motive n → motive (n + 1)) →
    (t : ℕ) → motive t :=
  fun {motive} zero succ t ↦ Nat.rec zero succ t
