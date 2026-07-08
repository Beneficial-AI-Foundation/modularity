import Mathlib.Data.List.Perm.Basic
import DeductiveVericoding.ListLanguage.Basic

open ListLanguage

/-- List implementation: transforms a list to a list (no parameter).
    - inTpe: `.list`, outTpe: `.list`
    - Code type: `.arrow .list .list` (function from list to list)
    - Correctness: `Pre inp → Post inp hpre (code.eval inp)` -/
abbrev ListImpl (Pre : List Nat → Prop) (Post : (inp : List Nat) → Pre inp → List Nat → Prop) :=
  Impl Unit .list .list (fun _ => Pre) (fun _ => Post)

/-- Base case implementation: produces a list from unit input.
    - inTpe: `.unit`, outTpe: `.list`
    - Code type: `.arrow .unit .list`
    - Post: `Inv [] out` -/
abbrev BaseImpl (Inv : List Nat → List Nat → Prop) :=
  Impl Unit .unit .list
    (fun _ _ => True)
    (fun _ _ _ out => Inv [] out)

/-- Step case implementation: parameterized by `tail : List Nat`.
    - inTpe: `.pair .nat .list` (a, sorted_tail)
    - outTpe: `.list`
    - Code type: `.arrow (.pair .nat .list) .list`
    - Pre: `Inv tail sorted_tail`
    - Post: `Inv (a :: tail) out` -/
abbrev StepImpl (Inv : List Nat → List Nat → Prop) :=
  Impl (List Nat) (.pair .nat .list) .list
    (fun tail ⟨_, sorted_tail⟩ => Inv tail sorted_tail)
    (fun tail ⟨a, _⟩ _ out => Inv (a :: tail) out)

/-! ## Ordered Predicate -/

def Ordered : List Nat → Prop
  | [] => True
  | [_] => True
  | x :: y :: xs => x ≤ y ∧ Ordered (y :: xs)

/-- Insert implementation: inserts an element into a sorted list.
    - inTpe: `.pair .nat .list` (element, sorted_list)
    - outTpe: `.list`
    - Code type: `.arrow (.pair .nat .list) .list`
    - Pre: input list is sorted
    - Post: output is sorted and a permutation of (a :: l) -/
abbrev InsertImpl :=
  Impl Unit (.pair .nat .list) .list
    (fun _ ⟨_, l⟩ => Ordered l)
    (fun _ ⟨a, l⟩ _ out => Ordered out ∧ List.Perm (a :: l) out)

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

/-! ## Sorted Invariant -/

/-- The sorting invariant: output is sorted and a permutation of input -/
def Sorted (inp out : List Nat) : Prop :=
  Ordered out ∧ List.Perm inp out

/-! ## The List Induction Combinator -/

/-- List case precondition: always true -/
def ListPre (_l : List Nat) : Prop := True

/-- List case postcondition: Inv inp out -/
def ListPost (Inv : List Nat → List Nat → Prop) (l : List Nat) (_hpre : ListPre l) (out : List Nat) : Prop := Inv l out

/-- The list induction combinator.

    Given:
    - `base : BaseImpl Inv` proving `Inv [] (base.code.eval ())`
    - `step : StepImpl Inv` proving the step preserves the invariant

    We construct a `ListImpl` with the combined correctness proof.

    This is Theorem A.2.1 from Jin-Xing Lim's thesis. -/
def listRecImpl
    (Inv : List Nat → List Nat → Prop)
    (base : BaseImpl Inv)
    (step : StepImpl Inv)
    : ListImpl ListPre (ListPost Inv) :=
  { code := Trm.listRec base.code step.code
    correct := fun _par inp _hpre => by
      simp only [ListPost, Trm.eval]
      induction inp with
      | nil => exact base.correct () () trivial
      | cons a tail ih => exact step.correct tail (a, _) (ih trivial)
  }

/-! ## Insertion Sort Impl -/

/-- Base implementation: `λ _ => []` produces empty list. -/
def nilImpl : BaseImpl Sorted :=
  { code := fun {_rep} => Trm'.lam fun _ => Trm'.nil
    correct := fun _ () _ => ⟨trivial, .refl _⟩ }

/-! ## Synthesized Insert using listRec -/

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

/-- Synthesized insert implementation using listRec.

    Code: λ (a, l) => listRec (λ _ => [a]) (λ (h, rec) => if a ≤ h then a :: h :: tail rec else h :: rec) l

    The key insight: for sorted input, when a ≤ h, we have insertVal a t = a :: t,
    so tail (insertVal a t) = t, allowing us to recover the original tail. -/
def synthesizedInsert : InsertImpl :=
  { code := fun {rep} => Trm'.lam fun p =>
      let a := Trm'.fst (.var p)
      let l := Trm'.snd (.var p)
      Trm'.app
        (Trm'.listRec
          -- base: λ _ => [a]
          (Trm'.lam fun _ => Trm'.cons a Trm'.nil)
          -- step: λ (h, rec) => if a ≤ h then a :: h :: tail rec else h :: rec
          (Trm'.lam fun hr =>
            let h := Trm'.fst (.var hr)
            let result := Trm'.snd (.var hr)
            Trm'.ite (Trm'.le a h)
              (Trm'.cons a (Trm'.cons h (Trm'.tail result)))
              (Trm'.cons h result)))
        l
    correct := fun _ ⟨a, l⟩ hl => by
      -- The synthesized code evaluates to insertVal a l
      -- We prove equivalence and use existing theorems
      have heq : ∀ l, Ordered l → Trm'.eval.go [a]
          (fun v => bif Nat.ble a v.1 then a :: v.1 :: (match v.2 with | [] => [] | _ :: tl => tl)
                    else v.1 :: v.2) l = insertVal a l := by
        intro l hl'
        induction l with
        | nil => rfl
        | cons h t ih =>
          simp only [insertVal, Trm'.eval.go]
          have ht_ord : Ordered t := by cases t <;> simp_all [Ordered]
          cases Nat.decLe a h with
          | isTrue hle =>
            -- a ≤ h: Nat.ble a h = true, bif evaluates to first branch
            have h_insert_eq : insertVal a t = a :: t := insertVal_le_cons a h t hl' hle
            have hble : Nat.ble a h = true := Nat.ble_eq.mpr hle
            simp only [ih ht_ord, h_insert_eq, hble, cond_true, hle, ite_true]
          | isFalse hle =>
            -- a > h: Nat.ble a h = false, bif evaluates to second branch
            have hble : Nat.ble a h = false :=
              Bool.eq_false_iff.mpr (fun h => hle (Nat.ble_eq.mp h))
            simp only [ih ht_ord, hble, cond_false, hle, ite_false]
      simp only [Trm.eval, Trm'.eval]
      have hl' : Ordered l := hl
      convert And.intro (insertVal_sorted a l hl') (insertVal_perm a l) using 2 <;>
        exact heq l hl'
  }

-- Pretty print the synthesized insert code
#eval Trm.pretty synthesizedInsert.code
-- "(λ x0 : (Nat × List) => listRec((λ x1 : Unit => x0.1 :: []), (λ x2 : (Nat × List) => if x0.1 ≤ x2.1 then x0.1 :: x2.1 :: tail(x2.2) else x2.1 :: x2.2))(x0.2))"

/-! ## Tactic -/

/-- Tactic for synthesizing verified list implementations.
    Repeatedly tries to apply combinators (listRecImpl) and implementations (nilImpl, insertImpl). -/
macro "vericode" : tactic =>
  `(tactic| repeat any_goals first | refine listRecImpl _ ?_ ?_ | refine nilImpl | refine insertImpl)

/-! ## Summary

### PHOAS-Style Typed Terms

Following Chlipala's Parametric Higher-Order Abstract Syntax (PHOAS) approach,
we define terms parameterized by a variable representation:

```
inductive Tpe where
  | unit | nat | list | pair : Tpe → Tpe → Tpe | arrow : Tpe → Tpe → Tpe

inductive Trm' (rep : Tpe → Type) : Tpe → Type where
  | unit : Trm' rep .unit
  | nil : Trm' rep .list
  | num : Nat → Trm' rep .nat
  | var : {t : Tpe} → rep t → Trm' rep t
  | mkPair : Trm' rep t → Trm' rep u → Trm' rep (.pair t u)
  | fst : Trm' rep (.pair t u) → Trm' rep t
  | snd : Trm' rep (.pair t u) → Trm' rep u
  | lam : (rep t → Trm' rep u) → Trm' rep (.arrow t u)
  | app : Trm' rep (.arrow t u) → Trm' rep t → Trm' rep u
  | insert : Trm' rep .nat → Trm' rep .list → Trm' rep .list
  | listRec : Trm' rep (.arrow .unit .list) → Trm' rep (.arrow (.pair .nat .list) .list)
            → Trm' rep (.arrow .list .list)

def Trm (t : Tpe) := {rep : Tpe → Type} → Trm' rep t  -- Closed terms
```

Key benefits of PHOAS:
- **No context lookup**: Variables hold their values directly when `rep = Tpe.denote`
- **Lean handles substitution**: Lambda application is just Lean function application
- **Type-safe pretty printing**: Use `rep = fun _ => String` for variable names

### Evaluation without Context

```
def Trm'.eval : Trm' Tpe.denote t → t.denote
  | .var x => x  -- x is already the value!
  | .lam f => fun v => (f v).eval  -- Lean handles binding
  | .listRec base step => ...  -- returns a function List → List
  ...
```

### Generalized Implementation Structure

Implementations use DSL types directly:

```
structure Impl (ParBase : Type) (inTpe outTpe : Tpe)
    (Pre : ParBase → inTpe.denote → Prop)
    (Post : (par : ParBase) → (inp : inTpe.denote) → Pre par inp → outTpe.denote → Prop) where
  code : Trm (.arrow inTpe outTpe)           -- Code is always a function
  correct : ∀ par inp hpre, Post par inp hpre (code.eval inp)
```

The `ParBase` parameter allows correctness to be parameterized (e.g., by a tail list).

Specializations:

```
abbrev ListImpl Pre Post := Impl Unit .list .list (fun _ => Pre) (fun _ => Post)
-- inTpe = .list, outTpe = .list, code : Trm (.arrow .list .list)

abbrev BaseImpl Inv := Impl Unit .unit .list (fun _ _ => True) (fun _ _ _ out => Inv [] out)
-- inTpe = .unit, outTpe = .list, code : Trm (.arrow .unit .list)

abbrev StepImpl Inv := Impl (List Nat) (.pair .nat .list) .list
    (fun tail ⟨_, sorted_tail⟩ => Inv tail sorted_tail)
    (fun tail ⟨a, _⟩ _ out => Inv (a :: tail) out)
-- ParBase = List Nat, inTpe = .pair .nat .list, outTpe = .list
```

The `correct` field proves: `Pre par inp → Post par inp hpre (code.eval inp)`.

### List Induction Combinator

The `listRecImpl` combinator constructs a `ListImpl` from base and step implementations:

```
def listRecImpl (Inv : List Nat → List Nat → Prop)
    (base : BaseImpl Inv)
    (step : StepImpl Inv)
    : ListImpl ListPre (ListPost Inv)
```

The combinator:
1. Combines `base.code` and `step.code` into a `listRec` term
2. Proves correctness by induction using `base.correct` and `step.correct`

For sorting, `Sorted inp out = Ordered out ∧ List.Perm inp out`.

### References

- Adam Chlipala, "Parametric Higher-Order Abstract Syntax for Mechanized Semantics" (ICFP 2008)
- Adam Chlipala, "Certified Programming with Dependent Types"
- Jin-Xing Lim, "Formalization of divide-and-conquer algorithm in Coq" (Appendix A)
-/
