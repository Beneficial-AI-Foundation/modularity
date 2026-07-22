import Mathlib.Data.List.Perm.Basic
import DeductiveVericoding.ListLanguage.Parametrized.Tactics

open ListLanguage

namespace Parametrized

def Ordered : List Nat → Prop
  | [] => True
  | [_] => True
  | x :: y :: xs => x ≤ y ∧ Ordered (y :: xs)

/-- The sorting invariant: output is sorted and a permutation of input -/
def Sorted (inp out : List Nat) : Prop := Ordered out ∧ (List.Perm inp out)

/- ## Properties for the base case -/

lemma NilSorted_iff (out : List Nat) : Sorted [] out ↔ out = [] := by
  simp only [Sorted, List.nil_perm, and_iff_right_iff_imp]
  intro h
  rw [h]
  trivial

/- ## Properties for the step case-/

lemma Sorted_push (a : Nat) (l res out : List Nat) :
   (Ordered res → Sorted (a :: res) out) → (Sorted l res → Sorted (a :: l) out) := by
  intro h hs
  specialize h hs.1
  use h.1, List.Perm.trans (List.Perm.cons a hs.2) h.2

lemma Sorted_Ordered (l : List Nat) :
    Ordered l → Sorted l l := by
  intro h
  use h

lemma Ordered_tail {a : Nat} {l : List Nat} : Ordered (a :: l) → Ordered l := by
  intro h
  induction l with
  | nil => trivial
  | cons _ _ => exact h.2

lemma Ordered_head_le_tail {a : Nat} {l : List Nat} : Ordered (a :: l) → ∀ b ∈ l, a ≤ b := by
  intro h
  induction l generalizing a with
  | nil => simp
  | cons b l ih => simp [Ordered] at *; aesop; exact le_trans left (ih right a_1 a_2)

lemma Ordered_tail_iff {a : Nat} {l : List Nat} : (Ordered l ∧ (∀ b ∈ l, a ≤ b)) ↔ Ordered (a :: l):= by
  induction l generalizing a with
  | nil => simp [Ordered]
  | cons b l _ => simp [Ordered]; aesop; exact le_trans left <| Ordered_head_le_tail right a_2 a_3

lemma mem_list_of_perm (a : Nat) (l1 l2 : List Nat) (h : l1.Perm l2) : a ∈ l1 ↔ a ∈ l2 := by
  exact List.Perm.mem_iff h

/- # InsertionSort Vericoding -/

abbrev InsertionSortProblem := ImplP [] (.arrow .list .list) (fun _ f ↦ ∀ l, Sorted l (f l))

abbrev InsertProblem (Γ : Ctx) := ImplP Γ (.arrow .nat (.arrow .list .list)) (fun _ f ↦ ∀ a, ∀ l, Ordered l → Sorted (a :: l) (f a l))

def InsertionSolution (Γ : Ctx) : InsertProblem Γ := by
  introP
  listRecP
  · simp [Sorted, Ordered]
    apply RelaxCondPTactic (t:=.list) _ (fun env out => out = [(env.getT 0 .nat)])
    · apply ConsPTactic
      · apply ParPTactic
      apply NilPTactic
    simp only [forall_eq, Ordered, and_self, implies_true]

  apply IfThenElsePtactic' (fun env => Nat.ble (env.getT 3 .nat) (env.getT 0 .nat))
  · apply LePTactic
    · apply ParPTactic
    apply ParPTactic
  · apply UsePTactic (s:=.list) (fun env => (env.getT 3 .nat) :: (env.getT 0 .nat) :: (env.getT 1 .list))
    · intro env h1 h2 h3
      apply Sorted_Ordered
      simp at h1
      use h1
    apply ConsPTactic
    · apply ParPTactic
    apply ConsPTactic
    · apply ParPTactic
    apply ParPTactic

  apply UsePTactic (s:=.list) (fun env => (env.getT 0 .nat) :: (env.getT 2 .list))
  · intro env h1 h2 h3
    simp at h1
    specialize h2 (Ordered_tail h3)
    constructor
    · refine Ordered_tail_iff.1 ⟨h2.1, ?_⟩
      intro b hb
      simp [Env.getT] at hb
      have : env.get 2 = env.2.2.fst := rfl
      simp [this, ← List.Perm.mem_iff (a:=b) h2.2] at hb
      obtain rfl|hb := hb
      · exact le_of_lt h1
      exact (Ordered_tail_iff.2 h3).2 b hb
    exact List.Perm.trans (List.Perm.swap _ _ _) (List.Perm.cons _ h2.2)
  apply ConsPTactic
  · apply ParPTactic
  apply ParPTactic

def InsertionSortSolution : InsertionSortProblem := by
  listRecP
  · simp [NilSorted_iff]
    apply NilPTactic
  apply RelaxCondPTactic (t:= .list) _
   (fun env out => Ordered (env.getT 2 .list) → Sorted (env.getT 0 .nat :: env.getT 2 .list) out)
   ?_ (fun _ => Sorted_push _ _ _)
  apply AppPTactic .list .list (fun env => env.getT 2 .list) (fun env l out => Ordered l → Sorted (env.getT 0 .nat :: l) out)
  · apply ParPTactic
  apply AppPTactic .nat (.arrow .list .list) (fun env => env.getT 0 .nat) (fun env a f => ∀ l, Ordered l → Sorted (a :: l) (f l))
  · apply ParPTactic
  apply InsertionSolution
