import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.ZMod.Basic

-- Following http://adam.chlipala.net/theses/andreser.pdf chapter 3

-- -- Define runtime operations
-- @[simp] def runtime_mul := Int.mul
-- @[simp] def runtime_add := Int.add

-- -- Notation for runtime operations
-- infixl:70 (priority := high) " * " => runtime_mul
-- infixl:65 (priority := high) " + " => runtime_add

namespace Associational

-- Evaluation function for associational representation
def eval (p : List (Int × Int)) : Int :=
  List.foldr (fun t acc => t.1 * t.2 + acc) 0 p

-- Basic lemmas about eval
@[simp] lemma eval_nil : eval [] = 0 := rfl

@[simp] lemma eval_cons (p : Int × Int) (q : List (Int × Int)) :
  eval (p :: q) = p.1 * p.2 + eval q := rfl

@[simp] lemma eval_app (p q : List (Int × Int)) :
  eval (p ++ q) = eval p + eval q := by
  induction p with
  | nil =>
    simp [eval_nil, List.append]
  | cons a as ih =>
    simp [eval_cons, ih]
    ring

-- Map multiplication lemma
@[simp] lemma eval_map_mul (a x : Int) (p : List (Int × Int)) :
  eval (List.map (fun t => (a * t.1, x * t.2)) p) = a * x * eval p := by
  induction p with
  | nil =>
    simp [eval, List.map, List.foldr]
  | cons t ts ih =>
    simp at ih
    simp [eval_cons, ih]
    ring

-- Multiplication of associational representations
def mul (p q : List (Int × Int)) : List (Int × Int) :=
  List.flatMap (fun t =>
    List.map (fun t' => (t.1 * t'.1, t.2 * t'.2))
    q) p

@[simp] lemma eval_mul (p q : List (Int × Int)) :
  eval (mul p q) = eval p * eval q := by
  induction p with
  | nil => simp [mul, eval_nil]
  | cons t ts ih =>
    unfold mul at ih
    simp [mul, eval_cons, ih]
    ring

-- Example: base 10 2-digit multiplication
example (a0 a1 b0 b1 : Int) :
  ∃ ab, eval ab = eval [(10, a1), (1, a0)] * eval [(10, b1), (1, b0)] := by
  rw [←eval_mul]
  use (mul [(10, a1), (1, a0)] [(10, b1), (1, b0)])

-- Split function for reduction
def split (s : Int) (p : List (Int × Int)) : List (Int × Int) × List (Int × Int) :=
  let hi_lo := List.partition (fun t => t.1 % s == 0) p
  (hi_lo.2, List.map (fun t => (t.1 / s, t.2)) hi_lo.1)

lemma eval_split (s : Int) (p : List (Int × Int)) (s_nz : s ≠ 0) :
  eval (split s p).1 + s * eval (split s p).2 = eval p := by
  simp [split]
  induction p with
  | nil => simp
  | cons t ts ih =>
    simp [eval_cons]
    sorry
    -- by_cases h : t.1 % s == 0
    -- · simp [h, List.partition]
    --   ring_nf
    --   have hh := Int.mul_ediv_cancel_left t.1 s_nz
    --   rw [Int.mul_ediv_assoc]
    --   ring
    -- · simp [h, List.partition]
    --   ring

-- Reduction rule
lemma reduction_rule (a b s c : Int) (modulus_nz : s - c ≠ 0) :
  (a + s * b) % (s - c) = (a + c * b) % (s - c) := by
  have h : a + s * b = (a + c * b) + b * (s - c) := by ring
  rw [h]
  sorry
  -- rw [Int.add_mod, Int.mod_mul, Int.add_zero, Int.mod_mod]
  -- · rfl
  -- · exact modulus_nz

-- Reduce function
def reduce (s : Int) (c : List (Int × Int)) (p : List (Int × Int)) : List (Int × Int) :=
  let lo_hi := split s p
  lo_hi.1 ++ mul c lo_hi.2

@[simp] lemma eval_reduce (s : Int) (c : List (Int × Int)) (p : List (Int × Int))
    (s_nz : s ≠ 0) (modulus_nz : s - eval c ≠ 0) :
  eval (reduce s c p) % (s - eval c) = eval p % (s - eval c) := by
  simp [reduce]
  sorry
  -- rw [eval_app, eval_mul, eval_split s_nz]
  -- rw [reduction_rule _ _ _ _ modulus_nz]

end Associational
