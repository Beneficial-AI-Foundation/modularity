import Mathlib.Data.List.Perm.Basic

/-!
# Verified Sorting via List Induction

This module synthesizes correct-by-construction sorting algorithms using the
list induction principle, following the Codable pattern.

## Structure

1. **Type Universe**: `Tpe` - types in our DSL (unit, nat, list, pair, arrow)
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
- Base implementation: `BaseImpl Inv` proving `Inv [] (base.code.eval ())`
- Step implementation: `StepImpl Inv` proving the step preserves invariant

We construct: `ListImpl ListPre (ListPost Inv)`

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
  | bool : Tpe
  | nat : Tpe
  | list : Tpe
  | pair : Tpe → Tpe → Tpe
  | arrow : Tpe → Tpe → Tpe
  deriving Repr, BEq, DecidableEq

/-- Denotation of types to Lean types -/
def Tpe.denote : Tpe → Type
  | .unit => Unit
  | .bool => Bool
  | .nat => Nat
  | .list => List Nat
  | .pair t u => t.denote × u.denote
  | .arrow t u => t.denote → u.denote

/-- Default value for each type -/
instance instInhabitedDenote : (t : Tpe) → Inhabited t.denote
  | .unit => inferInstanceAs (Inhabited Unit)
  | .bool => inferInstanceAs (Inhabited Bool)
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
  -- Boolean operations
  | true : Trm' rep .bool
  | false : Trm' rep .bool
  | le : Trm' rep .nat → Trm' rep .nat → Trm' rep .bool
  | ite : {t : Tpe} → Trm' rep .bool → Trm' rep t → Trm' rep t → Trm' rep t
  -- List operations
  | head : Trm' rep .list → Trm' rep .nat   -- returns 0 for empty list
  | tail : Trm' rep .list → Trm' rep .list  -- returns [] for empty list

/-- Closed terms are polymorphic over all variable representations -/
def Trm (t : Tpe) := {rep : Tpe → Type} → Trm' rep t

/-- Smart constructor for closed listRec terms -/
def Trm.listRec (base : Trm (.arrow .unit .list)) (step : Trm (.arrow (.pair .nat .list) .list)) : Trm (.arrow .list .list) :=
  fun {_rep} => Trm'.listRec base step

/-- Pretty-print a type -/
def Tpe.pretty : Tpe → String
  | .unit => "Unit"
  | .bool => "Bool"
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
  | _, .true, n => ("true", n)
  | _, .false, n => ("false", n)
  | _, .le e1 e2, n =>
      let (s1, n1) := e1.prettyAux n
      let (s2, n2) := e2.prettyAux n1
      (s!"{s1} ≤ {s2}", n2)
  | _, .ite c t e, n =>
      let (sc, n1) := c.prettyAux n
      let (st, n2) := t.prettyAux n1
      let (se, n3) := e.prettyAux n2
      (s!"if {sc} then {st} else {se}", n3)
  | _, .head e, n =>
      let (s, n1) := e.prettyAux n
      (s!"head({s})", n1)
  | _, .tail e, n =>
      let (s, n1) := e.prettyAux n
      (s!"tail({s})", n1)

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
        | a :: tl => stepVal (a, go tl)
      go
  | _, .true => Bool.true
  | _, .false => Bool.false
  | _, .le e1 e2 => Nat.ble e1.eval e2.eval
  | _, .ite c t e => bif c.eval then t.eval else e.eval
  | _, .head e => match e.eval with | [] => (0 : Nat) | h :: _ => h
  | _, .tail e => match e.eval with | [] => [] | _ :: tl => tl

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

/-- Step implementation: `λ (a, sorted) => insert a sorted` preserves Sorted. -/
def insertImpl : StepImpl Sorted :=
  { code := fun {_rep} => Trm'.lam fun p =>
      Trm'.insert (.fst (.var p)) (.snd (.var p))
    correct := fun _tail ⟨a, sorted_tail⟩ ⟨h_ord, h_perm⟩ =>
      ⟨insertVal_sorted a sorted_tail h_ord,
       (h_perm.cons a).trans (insertVal_perm a sorted_tail)⟩ }

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

def synthesizedSort : ListImpl ListPre (ListPost Sorted) := by vericode

/-! ## Examples -/

-- Evaluate the synthesized sort
#eval synthesizedSort.code.eval [3, 1, 4, 1, 5, 9, 2, 6]
-- [1, 1, 2, 3, 4, 5, 6, 9]

-- Pretty print the synthesized code
#eval Trm.pretty synthesizedSort.code
-- "listRec((λ x0 : Unit => []), (λ x1 : (Nat × List) => insert(x1.1, x1.2)))"

-- Direct evaluation
example : synthesizedSort.code.eval [3, 1, 4] = [1, 3, 4] := rfl

-- Type information
#check synthesizedSort.code     -- Trm (.arrow .list .list)
#check synthesizedSort.correct  -- correctness proof

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

end InsertionSort
