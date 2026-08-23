import DeductiveVericoding.ListLanguage.InsertionSort

open ListLanguage

/-!
# Harder vericoding problems

Every specification in `Problems.lean` has the shape `out = f inp`: it names the answer, so a
derivation only ever has to *build* the named term and never has to decide anything. The problems
here are the opposite — each postcondition is a predicate relating `inp` and `out`, and most of
them admit **many** correct outputs. Solving one means committing to an implementation the
specification does not name, which is the step `relaxPost` exists for.

One limit of the DSL (`Basic.lean`) still shapes what can be asked here: there is **no
arithmetic** — `Trm'` has `num`, `le`, `ite`, `cons`, `head`, `tail` and `listRec`, but no `+`,
so no length, sum or count.

What is no longer a limit is the *result type of a fold*. `Trm'.listRec` now returns an arbitrary
`Tpe`, and `ListRecTactic`/`ListRecTactic'` were generalised with it, so the same list recursion
can produce a number, a boolean or a pair. The `## Folds at other types` section is what that
buys. The `.head`/`.tail` primitives still have no combinator in `Tactics.lean`, which is what
keeps several of the frontier problems out of reach.

See the frontier section at the bottom for the ones that are still unreachable, and why.

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

/-! ## Folds at other types

Everything above folds a list into a list. These fold it into a **number**, a **boolean** and a
**pair** — the shapes `listRec` could not express while it was pinned to `.list`. Nothing else
changed: the same `ListRecTactic`/`ListRecTactic'` rules fire, `natCases` still invents the
comparison, and `relaxPost` still does the specification-level step.

One thing to watch when writing a specification for this section: `relaxPost`'s implication path
elaborates the lemma with `forallMetaTelescopeReducing`, which unfolds the conclusion while it
telescopes. A `Post` whose body is a bare `∀` therefore gets *eaten* — the lemma's conclusion
comes out as the body of the quantifier instead of as `Post inp out`, and nothing matches. Every
specification below is headed by a conjunction for that reason; see frontier item 2. -/

/-- The largest element of a list, `0` for the empty list.

The first `list → nat` fold in the file. Relational on both sides — `out` is pinned down by being
an upper bound *and* a member — so neither conjunct alone determines the answer, and the search
has to discover that the two together force `max`.

`natCases` supplies the comparison. Its two `.nat` candidates in the step are the head `a` and the
**recursive result** `res`, which is a number only because `listRec` may now return one; comparing
those two is exactly the step of the algorithm. -/
def MaxListSpec : List Nat → Nat → Prop := fun l out =>
  (∀ x ∈ l, x ≤ out) ∧ (out = 0 ∨ out ∈ l)

abbrev MaxListProblem := Impl .list .nat (fun _ => True) MaxListSpec

theorem MaxListSpec_nil (out : Nat) (h : out = 0) : MaxListSpec [] out := by
  subst h; exact ⟨by simp, Or.inl rfl⟩

theorem MaxListSpec_keep (b : Nat) (l : List Nat) (res out : Nat) (hres : MaxListSpec l res)
    (hb : b ≤ res) (h : out = res) : MaxListSpec (b :: l) out := by
  subst h
  refine ⟨fun x hx => ?_, hres.2.imp id (by simp_all)⟩
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hb
  · exact hres.1 x hx

theorem MaxListSpec_new (b : Nat) (l : List Nat) (res out : Nat) (hres : MaxListSpec l res)
    (hb : ¬ b ≤ res) (h : out = b) : MaxListSpec (b :: l) out := by
  subst h
  refine ⟨fun x hx => ?_, Or.inr (by simp)⟩
  rcases List.mem_cons.mp hx with rfl | hx
  · exact le_refl _
  · exact le_trans (hres.1 x hx) (Nat.le_of_not_le hb)

def MaxListSolution : MaxListProblem := by
  vericode [MaxListSpec_nil, MaxListSpec_keep, MaxListSpec_new]

#eval ListLanguage.Trm.pretty MaxListSolution.code

/-- The smallest element of a **non-empty** list, the list being given as `a :: l`.

The minimum has no identity element to start a fold from — `0` works for `max` but there is no
largest `Nat` for `min`, and the DSL cannot test `l` for emptiness (see frontier item 4). Splitting
the head off into `ListRecTactic`'s *parameter* dodges that: the recursion runs over `l` with `a`
fixed, so the base case returns `a` rather than a sentinel.

That makes this the mirror image of `MaxListProblem`: same fold at `.nat`, but the parameter now
carries a value the base case needs, rather than being the dummy `.unit` of `ListRecTactic'`. -/
def MinSpec : Nat × List Nat → Nat → Prop := fun (a, l) out =>
  (out ≤ a ∧ ∀ x ∈ l, out ≤ x) ∧ (out = a ∨ out ∈ l)

abbrev MinProblem := Impl (.pair .nat .list) .nat (fun _ => True) MinSpec

theorem MinSpec_nil (a out : Nat) (h : out = a) : MinSpec (a, []) out := by
  subst h; exact ⟨⟨le_refl _, by simp⟩, Or.inl rfl⟩

theorem MinSpec_new (a b : Nat) (l : List Nat) (res out : Nat) (hres : MinSpec (a, l) res)
    (hb : b ≤ res) (h : out = b) : MinSpec (a, b :: l) out := by
  subst h
  refine ⟨⟨le_trans hb hres.1.1, fun x hx => ?_⟩, Or.inr (List.mem_cons_self ..)⟩
  rcases List.mem_cons.mp hx with rfl | hx
  · exact le_refl _
  · exact le_trans hb (hres.1.2 x hx)

theorem MinSpec_keep (a b : Nat) (l : List Nat) (res out : Nat) (hres : MinSpec (a, l) res)
    (hb : ¬ b ≤ res) (h : out = res) : MinSpec (a, b :: l) out := by
  subst h
  refine ⟨⟨hres.1.1, fun x hx => ?_⟩, hres.2.imp id (List.mem_cons_of_mem _)⟩
  rcases List.mem_cons.mp hx with rfl | hx
  · exact Nat.le_of_not_le hb
  · exact hres.1.2 x hx

def MinSolution : MinProblem := by
  vericode [MinSpec_nil, MinSpec_new, MinSpec_keep]

#eval ListLanguage.Trm.pretty MinSolution.code

/-- Are all elements of `l` at most `a`? The first `list → bool` fold.

Stated *soundly in both directions* rather than as an `Iff`, so the two conjuncts are separate
obligations and the derivation cannot satisfy one by ignoring the other. `AllLESpec_drop` needs no
hypothesis about the recursive result at all: once some element exceeds `a` the answer is `false`
whatever the tail did, and the derivation duly drops `res` on that branch — the boolean short
circuit falls out of the specification rather than being programmed in. -/
def AllLESpec : Nat × List Nat → Bool → Prop := fun (a, l) out =>
  (out = true → ∀ x ∈ l, x ≤ a) ∧ (out = false → ∃ x ∈ l, ¬ x ≤ a)

abbrev AllLEProblem := Impl (.pair .nat .list) .bool (fun _ => True) AllLESpec

theorem AllLESpec_nil (a : Nat) (out : Bool) (h : out = true) : AllLESpec (a, []) out := by
  subst h; exact ⟨by simp, by simp⟩

theorem AllLESpec_keep (a b : Nat) (l : List Nat) (res out : Bool)
    (hres : AllLESpec (a, l) res) (hb : b ≤ a) (h : out = res) : AllLESpec (a, b :: l) out := by
  subst h
  refine ⟨fun ht x hx => ?_, fun hf => ?_⟩
  · rcases List.mem_cons.mp hx with rfl | hx
    · exact hb
    · exact hres.1 ht x hx
  · obtain ⟨x, hx, hnx⟩ := hres.2 hf
    exact ⟨x, List.mem_cons_of_mem _ hx, hnx⟩

theorem AllLESpec_drop (a b : Nat) (l : List Nat) (out : Bool)
    (hb : ¬ b ≤ a) (h : out = false) : AllLESpec (a, b :: l) out := by
  subst h
  exact ⟨by simp, fun _ => ⟨b, List.mem_cons_self .., hb⟩⟩

def AllLESolution : AllLEProblem := by
  vericode [AllLESpec_nil, AllLESpec_keep, AllLESpec_drop]

#eval ListLanguage.Trm.pretty AllLESolution.code

/-- Partition `l` around the pivot `a`. A `list → pair` fold, and the one problem in this file
that was written up as unreachable *before* `listRec` was generalised.

Two things had to line up. `listRec` must return `.pair .list .list`, which it now can; and the
relational, `Perm`-coupled postcondition must still reach the `out = (…, …)` shape `PairTactic`
needs — which it does, because each `relaxPost` implication below fixes *both* components at once
(`out = (b :: res.1, res.2)`), so the coupling is discharged in the specification step and never
has to be split across two independent goals. -/
def PartSpec : Nat × List Nat → List Nat × List Nat → Prop := fun (a, l) out =>
  (out.1 ++ out.2).Perm l ∧ (∀ x ∈ out.1, x ≤ a) ∧ (∀ x ∈ out.2, ¬ x ≤ a)

abbrev PartProblem :=
  Impl (.pair .nat .list) (.pair .list .list) (fun _ => True) PartSpec

theorem PartSpec_nil (a : Nat) (out : List Nat × List Nat) (h : out = ([], [])) :
    PartSpec (a, []) out := by subst h; exact ⟨by simp, by simp, by simp⟩

theorem PartSpec_keep (a b : Nat) (l : List Nat) (res out : List Nat × List Nat)
    (hres : PartSpec (a, l) res) (hb : b ≤ a) (h : out = (b :: res.1, res.2)) :
    PartSpec (a, b :: l) out := by
  subst h
  obtain ⟨h1, h2, h3⟩ := hres
  exact ⟨by simpa using h1.cons b, by grind, h3⟩

theorem PartSpec_drop (a b : Nat) (l : List Nat) (res out : List Nat × List Nat)
    (hres : PartSpec (a, l) res) (hb : ¬ b ≤ a) (h : out = (res.1, b :: res.2)) :
    PartSpec (a, b :: l) out := by
  subst h
  obtain ⟨h1, h2, h3⟩ := hres
  refine ⟨?_, h2, by grind⟩
  simpa using (List.perm_middle.trans (h1.cons b))

def PartSolution : PartProblem := by
  vericode [PartSpec_nil, PartSpec_keep, PartSpec_drop]

#eval ListLanguage.Trm.pretty PartSolution.code

/-! ### Two accumulators in one pass

`MinMaxProblem` computes the minimum *and* the maximum of `a :: l` in a single traversal, by
folding at `.pair .nat .nat`. Unlike everything above it needs a **guided** derivation, and for a
sharply localised reason.

`natCases` builds its candidate comparisons from `decodeInputTpe`, which walks the *right-nested
spine* of the input type and keeps the components that are literally `.nat`. In the step here the
spine is `a`, `res`, `b`, `tl` with `res : .pair .nat .nat`, so `res` is one component of pair
type and its two halves are never offered. The only comparison `natCases` can invent is `a` versus
`b`, which is not a step of the algorithm.

So the two `CasesTactic` conditions are written out below, and every other step — the base case,
the boolean condition itself, and all three branches — is still left to `vericode`. Making this
one automatic is frontier item 1: have `natCases` enumerate the `.nat` *leaves* of the input
rather than the `.nat` components of its spine. -/

def MaxPSpec : Nat × List Nat → Nat → Prop := fun (a, l) out =>
  (a ≤ out ∧ ∀ x ∈ l, x ≤ out) ∧ (out = a ∨ out ∈ l)

def MinMaxSpec : Nat × List Nat → Nat × Nat → Prop := fun p out =>
  MinSpec p out.1 ∧ MaxPSpec p out.2

abbrev MinMaxProblem :=
  Impl (.pair .nat .list) (.pair .nat .nat) (fun _ => True) MinMaxSpec

/-- The minimum never exceeds the maximum. Needed by `MinMaxSpec_newMax`: knowing only that `b`
is above the running maximum, it still has to place `b` above the running minimum. -/
theorem MinMaxSpec_le (a : Nat) (l : List Nat) (out : Nat × Nat) (h : MinMaxSpec (a, l) out) :
    out.1 ≤ out.2 := le_trans h.1.1.1 h.2.1.1

theorem MinMaxSpec_nil (a : Nat) (out : Nat × Nat) (h : out = (a, a)) :
    MinMaxSpec (a, []) out := by
  subst h; exact ⟨⟨⟨le_refl _, by simp⟩, Or.inl rfl⟩, ⟨⟨le_refl _, by simp⟩, Or.inl rfl⟩⟩

theorem MinMaxSpec_keep (a b : Nat) (l : List Nat) (res out : Nat × Nat)
    (hres : MinMaxSpec (a, l) res) (h1 : ¬ b ≤ res.1) (h2 : b ≤ res.2) (h : out = res) :
    MinMaxSpec (a, b :: l) out := by
  subst h
  obtain ⟨⟨⟨hm1, hm2⟩, hm3⟩, ⟨⟨hM1, hM2⟩, hM3⟩⟩ := hres
  refine ⟨⟨⟨hm1, fun x hx => ?_⟩, hm3.imp id (List.mem_cons_of_mem _)⟩,
          ⟨⟨hM1, fun x hx => ?_⟩, hM3.imp id (List.mem_cons_of_mem _)⟩⟩
  · rcases List.mem_cons.mp hx with rfl | hx
    · exact Nat.le_of_not_le h1
    · exact hm2 x hx
  · rcases List.mem_cons.mp hx with rfl | hx
    · exact h2
    · exact hM2 x hx

theorem MinMaxSpec_newMin (a b : Nat) (l : List Nat) (res out : Nat × Nat)
    (hres : MinMaxSpec (a, l) res) (h1 : b ≤ res.1) (h : out = (b, res.2)) :
    MinMaxSpec (a, b :: l) out := by
  subst h
  obtain ⟨⟨⟨hm1, hm2⟩, hm3⟩, ⟨⟨hM1, hM2⟩, hM3⟩⟩ := hres
  refine ⟨⟨⟨le_trans h1 hm1, fun x hx => ?_⟩, Or.inr (List.mem_cons_self ..)⟩,
          ⟨⟨hM1, fun x hx => ?_⟩, hM3.imp id (List.mem_cons_of_mem _)⟩⟩
  · rcases List.mem_cons.mp hx with rfl | hx
    · exact le_refl _
    · exact le_trans h1 (hm2 x hx)
  · rcases List.mem_cons.mp hx with rfl | hx
    · exact le_trans (le_trans h1 hm1) hM1
    · exact hM2 x hx

theorem MinMaxSpec_newMax (a b : Nat) (l : List Nat) (res out : Nat × Nat)
    (hres : MinMaxSpec (a, l) res) (h2 : ¬ b ≤ res.2) (h : out = (res.1, b)) :
    MinMaxSpec (a, b :: l) out := by
  subst h
  have hle : res.1 ≤ res.2 := MinMaxSpec_le a l res hres
  obtain ⟨⟨⟨hm1, hm2⟩, hm3⟩, ⟨⟨hM1, hM2⟩, hM3⟩⟩ := hres
  refine ⟨⟨⟨hm1, fun x hx => ?_⟩, hm3.imp id (List.mem_cons_of_mem _)⟩,
          ⟨⟨le_trans hM1 (Nat.le_of_not_le h2), fun x hx => ?_⟩,
           Or.inr (List.mem_cons_self ..)⟩⟩
  · rcases List.mem_cons.mp hx with rfl | hx
    · exact le_trans hle (Nat.le_of_not_le h2)
    · exact hm2 x hx
  · rcases List.mem_cons.mp hx with rfl | hx
    · exact le_refl _
    · exact le_trans (hM2 x hx) (Nat.le_of_not_le h2)

def MinMaxSolution : MinMaxProblem := by
  apply ListRecTactic
  · intro _ _ _ _; trivial
  · vericode [MinMaxSpec_nil]
  -- the head is below the running minimum: it becomes the new minimum
  refine CasesTactic (fun inp => Nat.ble inp.2.2.1 inp.2.1.1) (by vericode) ?_ ?_
  · vericode [MinMaxSpec_newMin]
  -- otherwise compare it against the running maximum
  refine CasesTactic (fun inp => Nat.ble inp.2.2.1 inp.2.1.2) (by vericode) ?_ ?_
  · vericode [MinMaxSpec_keep]
  vericode [MinMaxSpec_newMax]

#eval ListLanguage.Trm.pretty MinMaxSolution.code

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

What is still out of reach, and why. Generalising `listRec` retired the two entries that used to
head this list — a `list → nat` fold (now `MaxListProblem`) and a pair-valued fold
(now `PartProblem`) — so what remains is no longer about the *shape* of the recursion. Every item
below is a limit of the search or of the primitive set, and each is a benchmark target for one
specific missing piece.

**1. Comparisons buried inside a pair.** `natCases` gets its candidates from `decodeInputTpe`,
which walks the right-nested spine of the input type and keeps the components that are literally
`.nat`. A component of type `.pair .nat .nat` contributes nothing, so no comparison against either
half is ever offered. That is the whole reason `MinMaxSolution` is guided rather than automatic.
The fix is local — enumerate the `.nat` *leaves*, pairing each with the projection chain that
reaches it, instead of the `.nat` components of the spine — and it would also cover accumulators
like `.pair .bool .nat` needed by item 4.

**2. Specifications headed by a quantifier.** The obvious "any upper bound of a list":
```
abbrev BoundProblem := Impl .list .nat (fun _ => True) (fun l out => ∀ x ∈ l, x ≤ out)
```
is buildable — `MaxListSolution` is a witness — but cannot be *driven*. `relaxPost`'s implication
path elaborates its lemma with `forallMetaTelescopeReducing`, which reduces as it telescopes: the
conclusion `BoundSpec [] out` unfolds to `∀ x ∈ [], x ≤ out`, the telescope keeps going, and what
comes out is `?x ≤ ?out` instead of something matching `Post`. So the lemma is rejected before the
search starts. Conjunction-headed specifications sidestep it (hence the shape of every spec in the
folds section), but the honest fix is to stop the telescope at the arity of the lemma's own
binders rather than reducing through the conclusion.

**3. Anything needing an equality test** — deleting every copy of `a`, deduplication. Equality
*is* expressible in the DSL, as `ite (le a b) (ite (le b a) … …) …`, but it is unreachable for the
search: after the first split, `natCases` finds `Nat.ble a b` in the precondition, and
`comparesPair` then refuses *both* orders of that pair, so the second, nested split on the same
two numbers never happens. Deliberate — it is what stops the search splitting on one pair forever
— so lifting it means a finer criterion than "the precondition mentions this pair".

**4. Anything needing to test the tail for emptiness.** Two problems want it:
```
abbrev SortedProblem := Impl .list .bool (fun _ => True)
  (fun l out => (out = true → Ordered l) ∧ (out = false → ¬ Ordered l))
```
and the minimum of a possibly-empty list — `MinProblem` above only avoids it by moving the head
into the parameter. Both reduce to folding at `.pair .bool .nat`, carrying "is the tail empty"
next to the running value: `Ordered (a :: l)` is `Ordered l ∧ (l = [] ∨ a ≤ min l)`, and `min`
needs the same guard because it has no identity element. `listRec` can return that pair now, but
nothing can consume it — `head`/`tail` are `Trm'` constructors with no combinator in
`Tactics.lean`, and branching on a `.bool` *component of the input* is not something any rule
offers (`natCases` invents comparisons, never a boolean projection). A `HeadTactic`/`TailTactic`
pair — two-line mirrors of `FstTactic` — plus a `boolCases` rule would settle both.

**5. Folds that return a function.** The accumulator-passing reverse,
`rev l = fold (fun acc => acc) (fun res a _ => fun acc => res (a :: acc)) l []`, is a fold at
`s = .arrow .list .list`. This one is *half* unblocked and worth recording precisely, because the
remaining gap is small: `ListRecTactic'` accepts the arrow instantiation, and `vericode` already
closes the base case `∀ x, f x = [].reverse ++ x` on its own. The step goal
`∀ x, out x = tl.reverse ++ a :: x` is where it stops, because closing it means applying `res` —
a *function-valued component of the input*, known correct only from the precondition — to
`a :: x`. `AppTactic` cannot do that: its helper argument is required to be unconditional
(`fun _ => True`), which is exactly what makes `appList`/`introTac` work for helpers the search
*builds*. What is missing is the dual, an `AppSelfTactic` that applies an arrow-typed projection
of the input, with the precondition available to justify it.

**6. No arithmetic.** Length, sum and count remain unstatable as computations: `Trm'` has `num`
for literals but no successor or `+`, so nothing can produce a number it did not receive or
already name. `MaxListProblem` is only computable because the answer is always *an element of the
input*. -/
