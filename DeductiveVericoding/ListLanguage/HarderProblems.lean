import DeductiveVericoding.ListLanguage.InsertionSort

open ListLanguage

/-!
# Harder vericoding problems

Every specification in `Problems.lean` has the shape `out = f inp`: it names the answer, so a
derivation only ever has to *build* the named term and never has to decide anything. The problems
here are the opposite — each postcondition is a predicate relating `inp` and `out`, and most of
them admit **many** correct outputs. Solving one means committing to an implementation the
specification does not name, which is the step `relaxPost` exists for.

Two limits of the DSL (`Basic.lean`) shape what can be asked here:

* there is **no arithmetic** — `Trm'` has `num`, `le`, `ite`, `cons`, `head`, `tail` and
  `listRec`, but no `+`, so no length, sum or count;
* **`listRec` returns only `.list`**, and the `.head`/`.tail` primitives have no combinator in
  `Tactics.lean`, so a `list → nat` or `list → bool` fold cannot be built at all.

Hence: list-producing problems, plus small problems over numbers. See the frontier section at the
bottom for the ones that are out of reach, and why.

The other flagship relational problem is `InsertionSortProblem` in `InsertionSort.lean`;
`InsertionSolution'''` derives it from lemmas alone.
-/

/-! ## Warm-ups over numbers

No recursion, but the specification still leaves `vericode` a choice. -/

/-- Return *either* component. The minimal ambiguity: two correct answers and no reason to prefer
one. `vericode` takes the first. -/
def WitnessSpec (p : Nat × Nat) (out : Nat) : Prop := out = p.1 ∨ out = p.2

abbrev WitnessProblem := Impl (.pair .nat .nat) .nat (fun _ => True) WitnessSpec

theorem witness_left (p : Nat × Nat) (out : Nat) (h : out = p.1) : WitnessSpec p out := Or.inl h

def WitnessSolution : WitnessProblem := by vericode [witness_left]

#eval ListLanguage.Trm.pretty WitnessSolution.code

/-- Compare two numbers, but only *soundly*: the answer is pinned down except when `p.1 = p.2`,
where both booleans are correct. -/
def CmpSpec (p : Nat × Nat) (out : Bool) : Prop :=
  (out = true → p.1 ≤ p.2) ∧ (out = false → p.2 ≤ p.1)

abbrev CmpProblem := Impl (.pair .nat .nat) .bool (fun _ => True) CmpSpec

theorem cmp_true (p : Nat × Nat) (out : Bool) (h : p.1 ≤ p.2) (h2 : out = true) :
    CmpSpec p out := by subst h2; exact ⟨fun _ => h, by simp⟩

theorem cmp_false (p : Nat × Nat) (out : Bool) (h : ¬ p.1 ≤ p.2) (h2 : out = false) :
    CmpSpec p out := by subst h2; exact ⟨by simp, fun _ => Nat.le_of_not_le h⟩

def CmpSolution : CmpProblem := by vericode [cmp_true, cmp_false]

#eval ListLanguage.Trm.pretty CmpSolution.code

/-- *Any* upper bound of two numbers — infinitely many correct outputs. Without arithmetic the
only ones reachable are `p.1` and `p.2`, so the derivation is forced to compare them. -/
def UBSpec (p : Nat × Nat) (out : Nat) : Prop := p.1 ≤ out ∧ p.2 ≤ out

abbrev UBProblem := Impl (.pair .nat .nat) .nat (fun _ => True) UBSpec

theorem ub_left (p : Nat × Nat) (out : Nat) (h : p.2 ≤ p.1) (h2 : out = p.1) : UBSpec p out := by
  subst h2; exact ⟨le_refl _, h⟩

theorem ub_right (p : Nat × Nat) (out : Nat) (h : p.1 ≤ p.2) (h2 : out = p.2) : UBSpec p out := by
  subst h2; exact ⟨h, le_refl _⟩

def UBSolution : UBProblem := by vericode [ub_left, ub_right]

#eval ListLanguage.Trm.pretty UBSolution.code

/-- Sort a pair. A relational specification with a *pair-valued* output. -/
def OrderSpec (p : Nat × Nat) (out : Nat × Nat) : Prop :=
  out.1 ≤ out.2 ∧ (out = p ∨ out = (p.2, p.1))

abbrev OrderProblem := Impl (.pair .nat .nat) (.pair .nat .nat) (fun _ => True) OrderSpec

theorem order_id (p : Nat × Nat) (out : Nat × Nat) (h : p.1 ≤ p.2) (h2 : out = p) :
    OrderSpec p out := by subst h2; exact ⟨h, Or.inl rfl⟩

theorem order_swap (p : Nat × Nat) (out : Nat × Nat) (h : ¬ p.1 ≤ p.2) (h2 : out = (p.2, p.1)) :
    OrderSpec p out := by subst h2; exact ⟨Nat.le_of_not_le h, Or.inr rfl⟩

def OrderSolution : OrderProblem := by vericode [order_id, order_swap]

#eval ListLanguage.Trm.pretty OrderSolution.code

/-! ## Lists -/

/-- Return *any* permutation of the input — the most ambiguous specification in the file. The
identity is the cheapest witness, and that is what `vericode` finds. -/
abbrev PermProblem := Impl .list .list (fun _ => True) (fun l out => l.Perm out)

theorem perm_of_eq (l out : List Nat) (h : out = l) : l.Perm out := h ▸ List.Perm.refl l

def PermSolution : PermProblem := by vericode [perm_of_eq]

#eval ListLanguage.Trm.pretty PermSolution.code

/-- The last element of a list, `0` for the empty list. -/
def last : List Nat → Nat
  | [] => 0
  | [a] => a
  | _ :: l => last l

/-- Append `a` to the end of `l`, specified without saying where the other elements go: the
output is *some* rearrangement of `a :: l` whose last element is `a`.

The specification does not determine the output — `AppendSpec (1, [4,2,3])` holds of `[4,2,3,1]`
and of `[2,4,3,1]` alike — so no `Iff` can rewrite it into the `out = …` shape the code-building
combinators need. `AppendSpec_cons'` is instead consumed by `relaxPost`'s *implication* path: its
conclusion matches the postcondition, its first hypothesis is discharged from the precondition
(fixing `l2 := res`), and the survivor `out = b :: res` becomes the new postcondition. -/
def AppendSpec : Nat × List Nat → List Nat → Prop :=
  fun ⟨a, l⟩ out => List.Perm (a :: l) out ∧ last out = a

abbrev AppendProblem_hard := Impl (.pair .nat .list) .list (fun _ => True) AppendSpec

theorem AppendSpec_empty (a : Nat) (l : List Nat) : AppendSpec (a, []) l ↔ l = [a] := by
  simp [AppendSpec]
  aesop

theorem AppendSpec_cons (a b : Nat) (l1 l2 : List Nat) (h : AppendSpec (a, l1) l2) :
    AppendSpec (a, b :: l1) (b :: l2) := by
  induction l2
  · simp_all [AppendSpec]
  exact ⟨by grind [AppendSpec], h.2⟩

theorem AppendSpec_cons' (a b : Nat) (l1 l2 l3 : List Nat) (h : AppendSpec (a, l1) l2)
    (h2 : l3 = b :: l2) : AppendSpec (a, b :: l1) l3 :=
  h2 ▸ AppendSpec_cons a b l1 l2 h

def AppendSolution_hard : AppendProblem_hard := by
  vericode [AppendSpec_cons', AppendSpec_empty]

#eval ListLanguage.Trm.pretty AppendSolution_hard.code

/-- Keep exactly the elements of `l` that are `≤ a`, specified by sublist-ness and membership
rather than by `List.filter`.

Two things make this the hardest of the automatic problems. The comparison `b ≤ a` appears
*nowhere* in the specification, so `natCases` has to invent it. And the specification is still
ambiguous: for `l = [1, 1]` and `a = 5`, both `[1]` and `[1, 1]` satisfy it, since a sublist need
only contain *an* occurrence of each qualifying element. -/
def FilterSpec : Nat × List Nat → List Nat → Prop := fun (a, l) out =>
  out.Sublist l ∧ (∀ x ∈ out, x ≤ a) ∧ (∀ x ∈ l, x ≤ a → x ∈ out)

abbrev FilterProblem := Impl (.pair .nat .list) .list (fun _ => True) FilterSpec

theorem FilterSpec_nil (a : Nat) (out : List Nat) : FilterSpec (a, []) out ↔ out = [] := by
  constructor
  · rintro ⟨h, -, -⟩; exact List.sublist_nil.mp h
  rintro rfl; exact ⟨.slnil, by simp, by simp⟩

theorem FilterSpec_keep (a b : Nat) (l res out : List Nat) (hres : FilterSpec (a, l) res)
    (hb : b ≤ a) (h : out = b :: res) : FilterSpec (a, b :: l) out := by
  obtain ⟨h1, h2, h3⟩ := hres
  subst h
  refine ⟨h1.cons₂ _, ?_, ?_⟩ <;> grind

theorem FilterSpec_drop (a b : Nat) (l res out : List Nat) (hres : FilterSpec (a, l) res)
    (hb : ¬ b ≤ a) (h : out = res) : FilterSpec (a, b :: l) out := by
  obtain ⟨h1, h2, h3⟩ := hres
  subst h
  refine ⟨h1.cons _, ?_, ?_⟩ <;> grind

def FilterSolution : FilterProblem := by
  vericode [FilterSpec_nil, FilterSpec_keep, FilterSpec_drop]

#eval ListLanguage.Trm.pretty FilterSolution.code

/-! ## Merging two sorted lists

The one problem here that `vericode` cannot start on its own. Two reasons: the `ListRecTactic`
monotonicity obligation `Ordered (a :: l) → Ordered l` needs a `cases l` that no rule performs,
and the step needs an *insertion helper*, which the search has no way to invent. So it gets a
guided derivation in the style of `InsertionSortSolution`, reusing `InsertionSolution` outright. -/

def MergeSpec : List Nat × List Nat → List Nat → Prop := fun (l1, l2) out =>
  Ordered out ∧ (l1 ++ l2).Perm out

abbrev MergeProblem :=
  Impl (.pair .list .list) .list (fun p => Ordered p.1 ∧ Ordered p.2) MergeSpec

theorem MergeSpec_nil (l1 out : List Nat) (h : Ordered l1) :
    MergeSpec (l1, []) out ↔ out = l1 := by
  simp only [MergeSpec, List.append_nil]
  exact ⟨fun hs => (SortedOrdered_iff l1 out h).mp hs, fun he => by subst he; exact ⟨h, .refl _⟩⟩

def MergeSolution : MergeProblem := by
  apply ListRecTactic
  · rintro p a l ⟨h1, _⟩
    exact ⟨h1, by cases l <;> simp_all [Ordered]⟩
  · vericode [MergeSpec_nil]
  -- the merged tail `res` is already sorted, so merging `a` in is exactly an insertion
  refine RelaxPostTactic _ (fun (_l1, res, a, _l2) out => Sorted (a :: res) out) ?_ ?_
  · refine RelaxPreTactic (fun (_l1, res, _a, _l2) => Ordered res) (fun _ pre => pre.2.1) ?_
    refine SplitTactic (.pair .list (.pair .list (.pair .nat .list))) (.pair .nat .list) .list
      (fun (_l1, res, a, _l2) => (a, res)) (fun (a, res) out => Sorted (a :: res) out) ?_ ?_
    · vericode
    refine RelaxPreTactic (fun (_a, res) => Ordered res) ?_ ?_
    · intro (a, res) ⟨s, hs1, _⟩
      have : res = s.2.1 := by grind
      exact this ▸ hs1
    exact InsertionSolution
  rintro ⟨l1, res, a, l2⟩ ⟨-, -, hperm⟩ out ⟨ho, hp⟩
  exact ⟨ho, (List.perm_middle.trans (hperm.cons a)).trans hp⟩

#eval ListLanguage.Trm.pretty MergeSolution.code

/-! ## The frontier

Relational problems that cannot even be *stated as solvable* today. Each is a benchmark target
for a specific missing piece, recorded here rather than left as a failing build.

**1. An upper bound of a list.** Ambiguous in the same way as `UBProblem`, but over a list:
```
abbrev BoundProblem := Impl .list .nat (fun _ => True) (fun l out => ∀ x ∈ l, x ≤ out)
```
The `list → nat` fold now exists — `Trm'.listRec` returns an arbitrary `Tpe`, so `ListRecTactic`
can build it. What is still missing is the specification side: the postcondition is ambiguous
(any large enough `out` will do), so no rule can turn it into an `out = …` goal to build code for.

**2. Partition around a pivot.** A pair-valued output on a *coupled* relational specification:
```
def PartSpec : Nat × List Nat → List Nat × List Nat → Prop := fun (a, l) out =>
  (out.1 ++ out.2).Perm l ∧ (∀ x ∈ out.1, x ≤ a) ∧ (∀ x ∈ out.2, ¬ x ≤ a)
```
`listRec` can produce a pair now, but `PairTactic` needs a *functional* `out = (t1 inp, t2 inp)`,
so a relational pair postcondition cannot be split into two goals. That would need a `PairTactic'`
taking `Post1` and `Post2` separately — and even then the `Perm` clause couples the two
components, so the specification would have to be restated in a decoupled form first.

**3. Anything needing an equality test** — deleting every copy of `a`, deduplication. Equality
*is* expressible in the DSL, as `ite (le a b) (ite (le b a) … …) …`, but it is unreachable for the
search: after the first split, `natCases` finds `Nat.ble a b` in the precondition, and
`comparesPair` then refuses *both* orders of that pair, so the second, nested split on the same
two numbers never happens. Deliberate — it is what stops the search splitting on one pair forever
— so lifting it means a finer criterion than "the precondition mentions this pair". -/
