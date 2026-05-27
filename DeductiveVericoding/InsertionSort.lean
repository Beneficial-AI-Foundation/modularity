import Mathlib.Data.List.Perm.Basic

/-!
# Verified Sorting via List Induction

This module synthesizes correct-by-construction sorting algorithms using the
list induction principle, following the Codable pattern.

## Structure

1. **Type Universe**: `Tpe` - types in our DSL (nat, list, arrow)
2. **PHOAS Syntax**: `Trm' rep : Tpe → Type` - Parametric Higher-Order Abstract Syntax
3. **Closed Terms**: `Trm t = {rep : Tpe → Type} → Trm' rep t`
4. **Context-free Semantics**: `Trm'.eval` - no variable lookup needed
5. **Refinement Types**: `Impl` with pre/postconditions as subtypes
6. **Combinator**: `listRecImpl` - the list induction principle

## PHOAS-Style Typed Terms

Following Chlipala's PHOAS approach, terms are parameterized by a variable
representation `rep : Tpe → Type`. This allows:
- **Evaluation**: instantiate `rep = Tpe.denote` so variables hold values directly
- **Pretty printing**: instantiate `rep = fun _ => String` for variable names
- **No context lookup**: Lean handles substitution automatically

```
inductive Trm' (rep : Tpe → Type) : Tpe → Type where
  | var : rep t → Trm' rep t
  | lam : (rep t → Trm' rep u) → Trm' rep (.arrow t u)  -- Lean function!
  | app : Trm' rep (.arrow t u) → Trm' rep t → Trm' rep u
  ...
```

## The List Induction Principle

Given `Inv : List Nat → List Nat → Prop` relating input to output:
- Base implementation: `BaseImpl BasePre (BasePost Inv)`
- Step implementation: `StepImpl (StepPre Inv) (StepPost Inv)`

We construct:
- `ListImpl ListPre (ListPost Inv)`

For sorting, `Sorted inp out = Ordered out ∧ List.Perm inp out`.

## References
- Adam Chlipala, "Parametric Higher-Order Abstract Syntax for Mechanized Semantics" (ICFP 2008)
- Adam Chlipala, "Certified Programming with Dependent Types"
- Jin-Xing Lim, "Formalization of divide-and-conquer algorithm in Coq" (Appendix A)
-/

namespace InsertionSort

/-! ## Type Universe (CPDT-style) -/

/-- Types in our DSL -/
inductive Tpe where
  | unit : Tpe
  | nat : Tpe
  | list : Tpe
  | pair : Tpe → Tpe → Tpe
  | arrow : Tpe → Tpe → Tpe
  deriving Repr, BEq, DecidableEq

/-- Denotation of types to Lean types -/
def Tpe.denote : Tpe → Type
  | .unit => Unit
  | .nat => Nat
  | .list => List Nat
  | .pair t u => t.denote × u.denote
  | .arrow t u => t.denote → u.denote

/-- Default value for each type - needed for partial functions -/
instance instInhabitedDenote : (t : Tpe) → Inhabited t.denote
  | .unit => inferInstanceAs (Inhabited Unit)
  | .nat => inferInstanceAs (Inhabited Nat)
  | .list => inferInstanceAs (Inhabited (List Nat))
  | .pair t u => ⟨(instInhabitedDenote t).default, (instInhabitedDenote u).default⟩
  | .arrow _t u => ⟨fun _ => (instInhabitedDenote u).default⟩

/-! ## Typed Trms (PHOAS-style) -/

/-- Typed terms using Parametric Higher-Order Abstract Syntax (PHOAS).
    Following Chlipala's approach, terms are parameterized by a variable
    representation `rep : Tpe → Type`. This allows:
    - Evaluation: instantiate `rep = Tpe.denote` so variables hold values directly
    - Pretty printing: instantiate `rep = fun _ => String` for variable names
    - No context lookup needed - Lean handles substitution automatically -/
inductive Trm' (rep : Tpe → Type) : Tpe → Type where
  | unit : Trm' rep .unit
  | nil : Trm' rep .list
  | num : Nat → Trm' rep .nat
  | cons : Trm' rep .nat → Trm' rep .list → Trm' rep .list
  | var : {t : Tpe} → rep t → Trm' rep t
  | insert : Trm' rep .nat → Trm' rep .list → Trm' rep .list
  | mkPair : {t u : Tpe} → Trm' rep t → Trm' rep u → Trm' rep (.pair t u)
  | fst : {t u : Tpe} → Trm' rep (.pair t u) → Trm' rep t
  | snd : {t u : Tpe} → Trm' rep (.pair t u) → Trm' rep u
  | lam : {t u : Tpe} → (rep t → Trm' rep u) → Trm' rep (.arrow t u)
  | app : {t u : Tpe} → Trm' rep (.arrow t u) → Trm' rep t → Trm' rep u
  | listRec : Trm' rep (.arrow .unit .list) → Trm' rep (.arrow (.pair .nat .list) .list) → Trm' rep (.arrow .list .list)

/-- Closed terms are polymorphic over all variable representations -/
def Trm (t : Tpe) := {rep : Tpe → Type} → Trm' rep t

/-- Smart constructor for closed listRec terms -/
def Trm.listRec (base : Trm (.arrow .unit .list)) (step : Trm (.arrow (.pair .nat .list) .list)) : Trm (.arrow .list .list) :=
  fun {_rep} => Trm'.listRec base step

/-- Pretty-print a type -/
def Tpe.pretty : Tpe → String
  | .unit => "Unit"
  | .nat => "Nat"
  | .list => "List"
  | .pair t u => s!"({t.pretty} × {u.pretty})"
  | .arrow t u => s!"({t.pretty} → {u.pretty})"

/-- Pretty-print a term with string variables.
    Uses a counter to generate fresh variable names. -/
def Trm'.prettyAux : {t : Tpe} → Trm' (fun _ => String) t → Nat → String × Nat
  | _, .unit, n => ("()", n)
  | _, .nil, n => ("[]", n)
  | _, .num k, n => (toString k, n)
  | _, .cons hd tl, n =>
      let (hds, n1) := hd.prettyAux n
      let (tls, n2) := tl.prettyAux n1
      (s!"{hds} :: {tls}", n2)
  | _, .var x, n => (x, n)
  | _, .insert e1 e2, n =>
      let (s1, n1) := e1.prettyAux n
      let (s2, n2) := e2.prettyAux n1
      (s!"insert({s1}, {s2})", n2)
  | _, .mkPair e1 e2, n =>
      let (s1, n1) := e1.prettyAux n
      let (s2, n2) := e2.prettyAux n1
      (s!"({s1}, {s2})", n2)
  | _, .fst e, n =>
      let (s, n1) := e.prettyAux n
      (s!"{s}.1", n1)
  | _, .snd e, n =>
      let (s, n1) := e.prettyAux n
      (s!"{s}.2", n1)
  | _, .lam (t := ty) f, n =>
      let name := s!"x{n}"
      let (body, n') := (f name).prettyAux (n + 1)
      (s!"(λ {name} : {ty.pretty} => {body})", n')
  | _, .app f arg, n =>
      let (fs, n1) := f.prettyAux n
      let (args, n2) := arg.prettyAux n1
      (s!"{fs}({args})", n2)
  | _, .listRec base step, n =>
      let (bs, n1) := base.prettyAux n
      let (ss, n2) := step.prettyAux n1
      (s!"listRec({bs}, {ss})", n2)

/-- Pretty-print a closed term -/
def Trm.pretty {t : Tpe} (e : Trm t) : String :=
  (e.prettyAux 0).1

instance {t : Tpe} : ToString (Trm t) := ⟨Trm.pretty⟩

/-! ## Semantics -/

def insertVal (a : Nat) : List Nat → List Nat
  | [] => [a]
  | h :: t => if a ≤ h then a :: h :: t else h :: insertVal a t

/-- Evaluate a term with `rep = Tpe.denote`.
    Variables hold their values directly - no context lookup needed!
    This is the key PHOAS insight: Lean handles substitution automatically.

    Termination: structural recursion on terms, with a nested recursion on
    the input list for `listRec` (using precomputed base/step values). -/
def Trm'.eval : {t : Tpe} → Trm' Tpe.denote t → t.denote
  | _, .unit => ()
  | _, .nil => []
  | _, .num n => n
  | _, .cons hd tl => hd.eval :: tl.eval
  | _, .var x => x  -- x is already the value!
  | _, .insert e1 e2 => insertVal e1.eval e2.eval
  | _, .mkPair e1 e2 => (e1.eval, e2.eval)
  | _, .fst e => e.eval.1
  | _, .snd e => e.eval.2
  | _, .lam f => fun v => (f v).eval  -- Lean handles binding
  | _, .app f arg => f.eval arg.eval
  | _, .listRec base step =>
      let baseVal := base.eval ()
      let stepVal := step.eval
      let rec go : List Nat → List Nat
        | [] => baseVal
        | a :: tail => stepVal (a, go tail)
      go

/-- Evaluate a closed term -/
def Trm.eval {t : Tpe} (e : Trm t) : t.denote :=
  (e (rep := Tpe.denote)).eval

/-! ## Impl -/

/-- General implementation structure with embedded correctness proof.

    Parameters:
    - `ParBase` : the parameter type (for parameterized correctness)
    - `inTpe` : the DSL input type
    - `outTpe` : the DSL output type
    - `Pre` : precondition on parameter and input
    - `Post` : postcondition relating parameter, input, and output (also receives proof of Pre)

    The code type is `.arrow inTpe outTpe`, so `code.eval : inTpe.denote → outTpe.denote`. -/
structure Impl (ParBase : Type) (inTpe outTpe : Tpe)
    (Pre : ParBase → inTpe.denote → Prop)
    (Post : (par : ParBase) → (inp : inTpe.denote) → Pre par inp → outTpe.denote → Prop) where
  /-- The term implementing the function -/
  code : Trm (.arrow inTpe outTpe)
  /-- Correctness: precondition implies postcondition after evaluation -/
  correct : ∀ (par : ParBase) (inp : inTpe.denote) (hpre : Pre par inp),
    Post par inp hpre (code.eval inp)

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

/-! ## Semantic Sorting Function -/

def insertionSortVal : List Nat → List Nat
  | [] => []
  | a :: l => insertVal a (insertionSortVal l)

/-- insertionSortVal satisfies Sorted -/
theorem insertionSortVal_correct : ∀ l, Sorted l (insertionSortVal l) := by
  intro l
  induction l with
  | nil => exact ⟨trivial, List.Perm.refl _⟩
  | cons a t ih =>
    exact ⟨insertVal_sorted a _ ih.1, (List.Perm.cons a ih.2).trans (insertVal_perm a _)⟩

/-! ## The List Induction Combinator -/

/-- List case precondition: always true -/
def ListPre (_l : List Nat) : Prop := True

/-- List case postcondition: Inv inp out -/
def ListPost (Inv : List Nat → List Nat → Prop) (l : List Nat) (_hpre : ListPre l) (out : List Nat) : Prop := Inv l out

/-- The list induction combinator.

    Given:
    - `base` : BaseImpl Inv proving `Inv [] (base.code.eval)`
    - `step` : StepImpl Inv proving the step preserves the invariant

    We construct a ListImpl with the combined correctness proof.

    This is Theorem A.2.1 from Jin-Xing Lim's thesis. -/
def listRecImpl
    (Inv : List Nat → List Nat → Prop)
    (base : BaseImpl Inv)
    (step : StepImpl Inv)
    : ListImpl ListPre (ListPost Inv) :=
  { code := Trm.listRec base.code step.code
    correct := fun _par inp _hpre => by
      simp only [ListPost, Trm.eval]
      -- Prove by induction on inp
      induction inp with
      | nil =>
        -- Base case: Inv [] (go []) = Inv [] (base.code.eval ())
        exact base.correct () () trivial
      | cons a tail ih =>
        -- Step case: Inv (a :: tail) (go (a :: tail))
        -- ih : ListPre tail → Inv tail (go tail)
        exact step.correct tail (a, _) (ih trivial)
  }

/-! ## Insertion Sort Impl -/

/-- Base implementation: nil produces [].
    Proves: Sorted [] [] -/
def nilImpl : BaseImpl Sorted :=
  { code := fun {_rep} => Trm'.lam fun _ => Trm'.nil
    correct := fun _ () _ => by
      simp only [Trm.eval, Trm'.eval, Sorted, Ordered]
      exact ⟨trivial, List.Perm.refl []⟩
  }

/-- Step implementation: insert preserves Sorted.
    The step function is: λ (a, sorted) => insert a sorted
    Proves: Sorted tail sorted_tail → Sorted (a :: tail) (insertVal a sorted_tail) -/
def insertImpl : StepImpl Sorted :=
  { code := fun {_rep} => Trm'.lam fun p =>
      Trm'.insert (Trm'.fst (Trm'.var p)) (Trm'.snd (Trm'.var p))
    correct := fun tail ⟨a, sorted_tail⟩ ⟨h_ord, h_perm⟩ => by
      simp only [Trm.eval, Trm'.eval, Sorted]
      constructor
      · exact insertVal_sorted a sorted_tail h_ord
      · exact (h_perm.cons a).trans (insertVal_perm a sorted_tail)
  }

/-- Verified insertion sort -/
def insertionSort : ListImpl ListPre (ListPost Sorted) :=
  listRecImpl Sorted nilImpl insertImpl

/-! ## Tactic -/

macro "vericode" : tactic =>
  `(tactic| exact listRecImpl Sorted nilImpl insertImpl)

def synthesizedSort : ListImpl ListPre (ListPost Sorted) := by vericode

/-! ## Examples -/

#eval insertionSortVal [3, 1, 4, 1, 5, 9, 2, 6]

-- Pretty print the synthesized code
-- Note: Can't eval due to sorry in correctness proofs
-- #eval! Trm.pretty insertionSort.code

-- Direct evaluation using semantic function
example : insertionSortVal [3, 1, 4] = [1, 3, 4] := rfl

-- Type information
#check insertionSort.code     -- Trm (.arrow .list .list)
#check insertionSort.correct  -- correctness proof

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
partial def Trm'.eval : Trm' Tpe.denote t → t.denote
  | .var x => x  -- x is already the value!
  | .lam f => fun v => (f v).eval  -- Lean handles binding
  | .listRec base step => fun input => ...  -- returns a function
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
    (base : BaseImpl (Inv []))
    (step : StepImpl Inv)
    : ListImpl ListPre (ListPost Inv)
```

The combinator:
1. Combines `base.code` and `step.code` into a `listRec` term
2. Constructs the correctness proof using `base.correct` and `step.correct`

For sorting, `Sorted inp out = Ordered out ∧ List.Perm inp out`.

### References

- Adam Chlipala, "Parametric Higher-Order Abstract Syntax for Mechanized Semantics" (ICFP 2008)
- Adam Chlipala, "Certified Programming with Dependent Types"
- Jin-Xing Lim, "Formalization of divide-and-conquer algorithm in Coq" (Appendix A)
-/

end InsertionSort
