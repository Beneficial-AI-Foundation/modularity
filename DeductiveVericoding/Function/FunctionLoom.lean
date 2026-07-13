import Loom.MonadAlgebras.WP.Basic

/-!
# Codable: Verified Printable Programs

This module provides a framework for synthesizing correct-by-construction programs
that can be pretty-printed. Programs are represented as `Fctn` (functions) which
take a natural number as input and return an expression result.

## Key Types
- `Val`: Runtime values (naturals and strings)
- `Expr`: Pure expressions that evaluate to values (can reference the function argument)
- `Fctn`: A function from `Nat` to an expression
- `Codable P Q`: A verified function with precondition `P n` and postcondition `Q n result`

## Combinators
Build verified programs compositionally:
- `showArg`: Convert the function argument to its string representation
- `showNat`: Convert a literal natural number to its string representation
- `str`: Return a string literal
- `append`: Concatenate two string-producing programs
-/

/-! ## Section 1: Syntax -/

/-- Runtime values: naturals or strings -/
inductive Val where
  | nat : Nat → Val
  | str : String → Val
  deriving Repr, BEq, DecidableEq

/-- Expressions: pure computations that evaluate to values -/
inductive Expr where
  | val : Val → Expr                    -- literal value
  | arg : Expr                          -- the function's input argument
  | toStr : Expr → Expr                 -- convert to string
  | append : Expr → Expr → Expr         -- string concatenation
  deriving Repr, BEq

/-- A function takes a natural number and returns an expression -/
structure Fctn where
  body : Expr
  deriving Repr, BEq

/-! ## Section 2: Pretty Printing -/

def Val.pretty : Val → String
  | .nat n => s!"{n}"
  | .str s => s!"\"{s}\""

def Expr.pretty : Expr → String
  | .val v => v.pretty
  | .arg => "n"
  | .toStr e => s!"toString({e.pretty})"
  | .append e1 e2 => s!"{e1.pretty} ++ {e2.pretty}"

def Fctn.pretty (f : Fctn) : String := s!"fun n => {f.body.pretty}"

instance : ToString Val := ⟨Val.pretty⟩
instance : ToString Expr := ⟨Expr.pretty⟩
instance : ToString Fctn := ⟨Fctn.pretty⟩

/-! ## Section 3: Evaluation -/

/-- Evaluate an expression to a value, given the function argument -/
def Expr.eval (input : Nat) : Expr → Val
  | .val v => v
  | .arg => .nat input
  | .toStr e =>
      match e.eval input with
      | .nat n => .str (Nat.repr n)
      | .str s => .str s
  | .append e1 e2 =>
      match e1.eval input, e2.eval input with
      | .str s1, .str s2 => .str (s1 ++ s2)
      | .str s1, .nat n2 => .str (s1 ++ Nat.repr n2)
      | .nat n1, .str s2 => .str (Nat.repr n1 ++ s2)
      | .nat n1, .nat n2 => .str (Nat.repr n1 ++ Nat.repr n2)

def Fctn.eval (f : Fctn) (n : Nat) : Val := f.body.eval n

/-- Monadic evaluation for weakest precondition reasoning -/
def Fctn.evalM (f : Fctn) (n : Nat) : Id Val := pure (f.body.eval n)

/-! ## Section 4: Codable Programs -/

/-- A Codable is a function paired with a correctness proof.
    The proof shows that for all inputs `n`, given precondition `P n`,
    the result satisfies postcondition `Q n result`. -/
structure Codable (P : Nat → Prop) (Q : Nat → Val → Prop) where
  fctn : Fctn
  correctness : ∀ n, triple (m := Id) (l := Prop) (P n) (fctn.evalM n) (Q n)

/-! ## Section 5: Combinators

These combinators build verified programs compositionally.
Each combinator constructs both the syntax and its correctness proof. -/

/-- Convert the function argument to its string representation -/
def showArg {P : Nat → Prop} : Codable P (fun n res => res = .str (Nat.repr n)) :=
  { fctn := ⟨.toStr .arg⟩
    correctness := by
      intro n
      simp only [triple, wp, Fctn.evalM, Expr.eval, pure, liftM, monadLift,
                 MAlg.lift, MAlg.μ, MAlgOrdered.μ, Functor.map, id]
      intro _; trivial }

/-- Convert a literal natural number to its string representation -/
def showNat {P : Nat → Prop} (m : Nat) : Codable P (fun _ res => res = .str (Nat.repr m)) :=
  { fctn := ⟨.toStr (.val (.nat m))⟩
    correctness := by
      intro n
      simp only [triple, wp, Fctn.evalM, Expr.eval, pure, liftM, monadLift,
                 MAlg.lift, MAlg.μ, MAlgOrdered.μ, Functor.map, id]
      intro _; trivial }

/-- Return a string literal -/
def str {P : Nat → Prop} (s : String) : Codable P (fun _ res => res = .str s) :=
  { fctn := ⟨.val (.str s)⟩
    correctness := by
      intro n
      simp only [triple, wp, Fctn.evalM, Expr.eval, pure, liftM, monadLift,
                 MAlg.lift, MAlg.μ, MAlgOrdered.μ, Functor.map, id]
      intro _; trivial }

/-- Concatenate two string-producing programs -/
def append {P : Nat → Prop} {x y : Nat → String}
    (r1 : Codable P (fun n res => res = .str (x n)))
    (r2 : Codable P (fun n res => res = .str (y n))) :
    Codable P (fun n res => res = .str (x n ++ y n)) :=
  { fctn := ⟨.append r1.fctn.body r2.fctn.body⟩
    correctness := by
      intro n hP
      -- Step 1: Extract correctness hypotheses from r1 and r2
      have hr1 := r1.correctness n hP
      have hr2 := r2.correctness n hP
      -- Step 2: Unfold WP to get hr1 : r1.fctn.body.eval n = .str (x n) (and similarly for hr2)
      simp only [wp, Fctn.evalM, liftM, monadLift,
                 MAlg.lift, MAlg.μ, MAlgOrdered.μ, Functor.map, id, pure] at hr1 hr2 ⊢
      -- Step 3: Simplify append evaluation using hr1 and hr2
      simp only [Expr.eval, hr1, hr2] }

/-! ## Section 6: Synthesis Tactic

The `vericode` tactic repeatedly applies combinators to synthesize a verified program. -/

/-- Tactic macro for synthesizing Codable programs -/
macro "vericode" : tactic =>
  `(tactic| repeat any_goals first | apply append | apply showArg | apply showNat | apply str)

/-! ## Section 7: Examples -/

/-- Convert the input to string and append "!" -/
def natToStringBang : Codable (fun _ => True) (fun n res => res = .str (Nat.repr n ++ "!")) := by
  vericode

-- Evaluate the synthesized program
#eval (natToStringBang).fctn.eval 42
-- Val.str "42!"

-- Print the synthesized program
#eval (natToStringBang).fctn.pretty
-- "fun n => toString(n) ++ \"!\""

/-- Always return "hello" regardless of input -/
def constHello : Codable (fun _ => True) (fun _ res => res = .str "hello") := by
  vericode

#eval constHello.fctn.eval 999
-- Val.str "hello"

#eval constHello.fctn.pretty
-- "fun n => \"hello\""
