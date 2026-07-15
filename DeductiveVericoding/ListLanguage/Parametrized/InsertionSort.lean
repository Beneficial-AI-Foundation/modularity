import Mathlib.Data.List.Perm.Basic
import DeductiveVericoding.ListLanguage.Parametrized.Tactics

open ListLanguage

namespace Parametrized

def insertVal (a : Nat) : List Nat → List Nat
  | [] => [a]
  | h :: t => if a ≤ h then a :: h :: t else h :: insertVal a t

def Ordered : List Nat → Prop
  | [] => True
  | [_] => True
  | x :: y :: xs => x ≤ y ∧ Ordered (y :: xs)

/-- The sorting invariant: output is sorted and a permutation of input -/
def Sorted (inp out : List Nat) : Prop := Ordered out ∧ (List.Perm inp out)

/- ## Properties of the base case -/

lemma NilSorted_iff (out : List Nat) : Sorted [] out ↔ out = [] := by
  simp only [Sorted, List.nil_perm, and_iff_right_iff_imp]
  intro h
  rw [h]
  trivial

/-! ## Properties of insertVal -/

theorem insertVal_ordered (a : Nat) (l : List Nat) (hs : Ordered l) :
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

/- # Sorting as a function -/

lemma Perm_trans {l1 l2 l3 : List Nat} : l1.Perm l2 → l2.Perm l3 → l1.Perm l3 := by
  sorry

lemma exists_sorted (inp : List Nat) : ∃! out, Sorted inp out := by
  induction inp with
  | nil => simp only [NilSorted_iff, existsUnique_eq]
  | cons a l ih =>
    obtain ⟨l', h1, h2⟩ := ih
    refine ⟨(insertVal a l'), ⟨insertVal_ordered a l' h1.1, ?_⟩, ?_⟩
    · apply Perm_trans (List.Perm.cons a h1.2) (insertVal_perm a l')
    sorry

noncomputable def sorted (l : List Nat) : List Nat := Classical.choose <| exists_sorted l

lemma Sorted_iff_eq_sorted (inp out : List Nat) : Sorted inp out ↔ out = sorted inp := by
  obtain ⟨out', h1, h2⟩ := exists_sorted inp
  refine ⟨fun h ↦ (Classical.choose_spec (exists_sorted inp)).2 _ h, fun h ↦ ?_⟩
  rw [h]
  apply (Classical.choose_spec (exists_sorted inp)).1

lemma sorted_cons (a : Nat) (l : List Nat) : sorted (a :: l) = insertVal a (sorted l) := by
  sorry

/- # InsertionSort Vericoding -/

abbrev InsertionSortProblem := ImplP [] (.arrow .list .list) (fun _ f ↦ ∀ l, Sorted l (f l))

abbrev InsertProblem := ImplP [] (.arrow .nat (.arrow .list .list)) (fun _ f ↦ ∀ a, ∀ l, Ordered l → Sorted (a :: l) (f a l))

def InsertionSolution : InsertProblem := by
  introP
  listRecP
  · simp [Sorted, Ordered]
    apply RelaxCondPTactic (t:=.list) _ (fun env out => out = [(env.getT 0 .nat)])
    · apply ConsPTactic
      · apply ParPTactic
      apply NilPTactic
    simp only [forall_eq, Ordered, and_self, implies_true]
  sorry




def InsertionSortSolution : InsertionSortProblem := by
  listRecP
  · simp [NilSorted_iff]
    apply NilPTactic
  simp [Sorted_iff_eq_sorted, sorted_cons]
  pushpreP
  apply AppPTactic _ .list .list (fun env => env.getT 2 .list) (fun env l out => out = insertVal (env.getT 0 Tpe.nat) l)
  · apply ParPTactic
  listRecP
  · apply ConsPTactic
    · apply ParPTactic
    apply NilPTactic
  sorry
