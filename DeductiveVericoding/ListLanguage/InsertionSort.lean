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

lemma Sorted_Cons (x : Nat) (l1 l2 l3 : List Nat) (h : l1.Perm l2) : Sorted (x :: l1) l3 ↔ Sorted (x :: l2) l3 :=
  SortedPerm_iff _ _ _ <| List.Perm.cons x h

lemma Sorted_Swap (x y : Nat) (l1 l2 : List Nat) : Sorted (x :: y :: l1) l2 ↔ Sorted (y :: x :: l1) l2 :=
  SortedPerm_iff _ _ _ <| List.Perm.swap y x l1

/-- All elements in a sorted list are ≥ its head -/
theorem Ordered_iff_all_ge_head (a : Nat) (l : List Nat) : Ordered (a :: l) ↔
    (∀ x ∈ l, a ≤ x) ∧ Ordered l := by
  induction l generalizing a with
  | nil => simp [Ordered]
  | cons b l ih =>
    simp [Ordered]
    intro hbl hab c hc
    exact le_trans hab <| ((ih b).mp hbl).1 c hc

/-- If `a` bounds `l1` from below and `l2` is an ordered rearrangement of `l1`, then `a :: l2`
is ordered. -/
lemma Ordered_cons_of_perm (a : Nat) (l1 l2 : List Nat) (hp : l1.Perm l2)
    (h1 : ∀ x ∈ l1, a ≤ x) (h2 : Ordered l2) : Ordered (a :: l2) :=
  (Ordered_iff_all_ge_head a l2).mpr ⟨fun x hx => h1 x (hp.mem_iff.mpr hx), h2⟩

lemma SortedOrdered_iff (l1 l2 : List Nat) (h : Ordered l1) : Sorted l1 l2 ↔ l2 = l1 := by
  refine ⟨fun h2 => ?_, fun h2 => by simp [Sorted, h2, h]⟩
  induction l1 generalizing l2 with
  | nil => simp_all only [Sorted, List.nil_perm]
  | cons a l1 ih =>
    induction l2 with
    | nil => simp_all only [Sorted, List.perm_nil, reduceCtorEq]
    | cons b l2 _ =>
      have hab : a = b := by
        apply le_antisymm
        · have : b = a ∨ b ∈ l1 := by grind [Sorted]
          obtain this|this := this
          · rw [this]
          exact ((Ordered_iff_all_ge_head a l1).mp h).1 b this
        have : a = b ∨ a ∈ l2 := by grind [Sorted]
        obtain this|this := this
        · rw [this]
        exact ((Ordered_iff_all_ge_head b l2).mp h2.1).1 a this
      simp_all [Sorted]
      apply ih
      · exact ((Ordered_iff_all_ge_head b l1).mp h).2
      · exact ((Ordered_iff_all_ge_head b l2).mp h2.1).2
      exact h2.2

/- # InsertionSort Vericoding -/

abbrev InsertionSortProblem := Impl .list .list (fun _ => True) (fun inp out => Sorted inp out)

abbrev InsertProblem := Impl (.pair .nat .list) .list (fun inp => Ordered inp.2) (fun ⟨a, l⟩ out => Sorted (a :: l) out)

def InsertionSolution : InsertProblem := by
  apply ListRecTactic
  · intro _ a l
    induction l with -- use grind here
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
  · simp
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
      change match inp with
      | (p, a, l, snd) => Sorted (p :: a :: l) (p :: a :: l)
      simp [SortedSelf_iff, Ordered] --grind here
      exact ⟨pre.2, pre.1.1⟩
  simp
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

/-- Same derivation as `InsertionSolution'`, but with every step below the case split left to
`vericode`: each lemma in the brackets is a search step that may rewrite the postcondition,
with the precondition available to discharge the lemma's own hypotheses. -/
def InsertionSolution'' : InsertProblem := by
  apply ListRecTactic
  · intro _ a l
    induction l with
    | nil => simp [Ordered]
    | cons a l _ => simp [Ordered]
  · vericode [SingletonSorted_iff]
  refine CasesTactic (fun inp => Nat.ble inp.1 inp.2.1) (by vericode) ?_ ?_
  -- `p ≤ a`: `p :: a :: l` is already ordered, so `Sorted (p :: a :: l) out` *is* `out = p :: a :: l`
  · simp
    vericode [SortedOrdered_iff, Ordered]
  -- `a < p`: swap, replace `p :: l` by the recursive result `res`, then read off `out = a :: res`
  vericode [Sorted_Swap, Sorted_Cons, SortedOrdered_iff, Ordered_cons_of_perm,
    Ordered_iff_all_ge_head]

/-- The whole `InsertProblem` in one search: `vericode` picks the list recursion, discharges its
monotonicity obligation, **invents the comparison to branch on**, and rewrites the postcondition
with the lemmas in each branch. The lemmas are the only input; no step of the derivation is
written by hand. -/
def InsertionSolution''' : InsertProblem := by
  vericode [SortedOrdered_iff, Sorted_Swap, Sorted_Cons,
    Ordered_cons_of_perm, Ordered_iff_all_ge_head, Ordered]

def InsertionSortSolution''' : InsertionSortProblem := by
  apply ListRecTactic'
  · vericode [SortedOrdered_iff]

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


-- this is a test for vericode, we would like to automate as much of the human written proof as possible
def InsertionSolution' : InsertProblem := by
  apply ListRecTactic
  · intro _ a l
    induction l with -- use grind here
    | nil => simp [Ordered]
    | cons a l _ => simp [Ordered]
  · vericode [SingletonSorted_iff]
  refine CasesTactic (fun inp => Nat.ble inp.1 inp.2.1) (by vericode) ?_ ?_
  · simp
    refine UseTactic (fun inp => inp.1 :: inp.2.1 :: inp.2.2.1) (by vericode) ?_
    intro inp pre
    change match inp with
    | (p, a, l, snd) => Sorted (p :: a :: l) (p :: a :: l)
    simp [SortedSelf_iff, Ordered] --grind here
    exact ⟨pre.2, pre.1.1⟩
  simp
  refine UseTactic (fun inp => inp.2.1 :: inp.2.2.2) (by vericode) ?_
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

-- pre1 pre2 pre3 Post
-- lemma h1 h2 ... => (Post' => Post)
-- pre1 pre2 pre3 Post'
