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

namespace ListLanguage

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
  | mkPair : {t u : Tpe} → Trm' rep t → Trm' rep u → Trm' rep (.pair t u)
  | fst : {t u : Tpe} → Trm' rep (.pair t u) → Trm' rep t
  | snd : {t u : Tpe} → Trm' rep (.pair t u) → Trm' rep u
  | lam : {t u : Tpe} → (rep t → Trm' rep u) → Trm' rep (.arrow t u)
  | app : {t u : Tpe} → Trm' rep (.arrow t u) → Trm' rep t → Trm' rep u
  | listRec {t s : Tpe} : Trm' rep (.arrow t s) →
   Trm' rep (.arrow (.pair t (.pair s (.pair .nat .list))) s) →
   Trm' rep (.arrow (.pair t .list) s)
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
  | _, .mkPair e1 e2 => (e1.eval, e2.eval)
  | _, .fst e => e.eval.1
  | _, .snd e => e.eval.2
  | _, .lam f => fun v => (f v).eval  -- Lean handles binding
  | _, .app f arg => f.eval arg.eval
  | _, .listRec base step => by
      expose_names
      intro p
      obtain ⟨par, l⟩ := p
      let baseVal := base.eval par
      let stepVal := step.eval
      let rec go : List Nat → s.denote
        | [] => baseVal
        | a :: tl => stepVal (par, (go tl, (a, tl)))
      exact go l
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
    - `inTpe` : the DSL input type
    - `outTpe` : the DSL output type
    - `Pre` : precondition on parameter and input
    - `Post` : postcondition relating parameter, input, and output (also receives proof of Pre)

    The code type is `.arrow inTpe outTpe`, so `code.eval : inTpe.denote → outTpe.denote`. -/
structure Impl (inTpe outTpe : Tpe)
    (Pre : inTpe.denote → Prop)
    (Post : inTpe.denote → outTpe.denote → Prop) where
  /-- The term implementing the function -/
  code : Trm (.arrow inTpe outTpe)
  /-- Correctness: precondition implies postcondition after evaluation -/
  correct : ∀ inp, Pre inp → Post inp (code.eval inp)

end ListLanguage
