import Mathlib.Data.List.Perm.Basic
import DeductiveVericoding.ListLanguage.Tactics

open ListLanguage

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

lemma SingletonSorted_iff (a : Nat) (out : List Nat) : Sorted [a] out ↔ out = [a] := by
  simp [Sorted]
  constructor
  · exact fun ⟨_, h⟩ => h.symm
  exact fun h => by simp [h, Ordered]

lemma SortedSelf_iff (l : List Nat) : Sorted l l ↔ Ordered l := by
  simp [Sorted]

lemma SortedPerm_iff (l1 l2 out : List Nat) (h : l1.Perm l2) : Sorted l1 out ↔ Sorted l2 out := by
  simp [Sorted]
  exact fun _ => ⟨fun h2 => List.Perm.trans h.symm h2, fun h2 => List.Perm.trans h h2⟩

/-- All elements in a sorted list are ≥ its head -/
theorem Ordered_iff_all_ge_head (a : Nat) (l : List Nat) : Ordered (a :: l) ↔
    (∀ x ∈ l, a ≤ x) ∧ Ordered l := by
  induction l generalizing a with
  | nil => simp [Ordered]
  | cons b l ih =>
    simp [Ordered]
    intro hbl hab c hc
    exact le_trans hab <| ((ih b).mp hbl).1 c hc

/- # InsertionSort Vericoding -/

abbrev InsertionSortProblem := Impl .list .list (fun _ => True) (fun inp out => Sorted inp out)

abbrev InsertProblem := Impl (.pair .nat .list) .list (fun inp => Ordered inp.2) (fun ⟨a, l⟩ out => Sorted (a :: l) out)

def InsertionSolution : InsertProblem := by
  apply ListRecTactic
  · intro _ a l
    induction l with
    | nil => simp [Ordered]
    | cons a l _ => simp [Ordered]
  · simp [SingletonSorted_iff]
    apply ConsTactic
    · apply IdentityTactic
    apply NilTactic
  refine CasesTactic (fun inp => Nat.ble inp.1 inp.2.1) ?_ ?_ ?_
  · apply LETactic
    · apply FstTactic
      apply IdentityTactic
    apply FstTactic
    apply SndTactic
    apply IdentityTactic
  simp
  refine UseTactic (fun inp => inp.1 :: inp.2.1 :: inp.2.2.1) ?_ ?_
  · apply ConsTactic
    · apply FstTactic
      apply IdentityTactic
    apply ConsTactic
    · apply FstTactic
      apply SndTactic
      apply IdentityTactic
    apply FstTactic
    apply SndTactic
    apply SndTactic
    apply IdentityTactic
  · intro inp pre
    simp [Sorted, Ordered, pre.2, pre.1.1]
    exact List.Perm.refl _
  refine UseTactic (fun inp => inp.2.1 :: inp.2.2.2) ?_ ?_
  · apply ConsTactic
    · apply FstTactic
      apply SndTactic
      apply IdentityTactic
    apply SndTactic
    apply SndTactic
    apply SndTactic
    apply IdentityTactic
  intro (p, a, l, res) pre
  simp_all [Sorted, Ordered_iff_all_ge_head]
  obtain ⟨⟨⟨hal, hl⟩, hpl⟩, hap⟩ := pre
  constructor
  · intro x hx
    have : x ∈ (p :: l) := by grind
    simp at this
    cases this with
    | inl h => exact h ▸ Nat.le_of_succ_le hap
    | inr h => exact hal x h
  apply List.Perm.trans (List.Perm.swap _ _ _)
  apply List.Perm.cons _ hpl.2

def InsertionSortSolution : InsertionSortProblem := by
  apply ListRecTactic'
  · refine UseTactic (fun inp => []) ?_ ?_
    · apply NilTactic
    simp [Sorted, Ordered]
  refine RelaxPostTactic _ (fun (a, l, res) out => Sorted (a :: res) out) ?_ ?_
  · refine RelaxPreTactic (fun (a, l, res) => Ordered res) ?_ (fun _ pre => pre.1)
    refine SplitTactic (.pair .nat (.pair .list .list)) (.pair .nat .list) .list (fun (a, l, res) => (a, res)) (fun (a, res) out => Sorted (a :: res) out) ?_ ?_
    · apply PairTactic
      · apply FstTactic
        apply IdentityTactic
      apply SndTactic
      apply SndTactic
      apply IdentityTactic
    refine RelaxPreTactic (fun (a, res) => Ordered res) ?_ ?_
    · exact InsertionSolution
    intro (a, res) ⟨s, hs1, hs2⟩
    have : res = s.2.2 := by grind
    exact this ▸ hs1
  intro (a, l, res) pre out
  exact (SortedPerm_iff _ _ _ (List.Perm.cons _ pre.2.symm)).mp
