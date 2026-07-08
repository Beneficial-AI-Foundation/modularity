/-!
# Function: Verified Printable Programs

This module provides a minimal framework for synthesizing correct-by-construction
programs that can be pretty-printed.

## Key Types
- `Val`: Runtime values (naturals and strings)
- `Expr`: Pure expressions that evaluate to values
- `Fctn`: A function from `Nat` to an expression
- `Spec A B`: A specification with precondition and postcondition
- `Implementation s`: A verified function satisfying specification `s`
- `Codable P Q`: Alias for `Implementation (mkSpec P Q)`

## Combinators
Build verified programs compositionally:
- `showArg`: Convert the function argument to its string representation
- `showNat`: Convert a literal natural number to its string representation
- `str`: Return a string literal
- `append`: Concatenate two string-producing programs
-/

namespace Function

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

/-! ## Section 4: Specifications -/

/-- A specification from type `A` to type `B` -/
structure Spec (A B : Type) where
  /-- Precondition on inputs -/
  pre : A → Prop
  /-- Postcondition relating inputs to outputs -/
  post : A → B → Prop

/-- Convert a precondition and postcondition to a specification -/
def mkSpec (P : Nat → Prop) (Q : Nat → Val → Prop) : Spec Nat Val :=
  { pre := P, post := Q }

/-! ## Section 5: Implementations -/

/-- A verified implementation of a specification.
    Consists of code and a proof that it satisfies the spec. -/
structure Implementation (s : Spec Nat Val) where
  /-- The syntactic code -/
  code : Fctn
  /-- Correctness: for all inputs satisfying the precondition,
      the output satisfies the postcondition -/
  correct : ∀ n, s.pre n → s.post n (code.eval n)

/-- Codable is an implementation of a specification -/
abbrev Codable (P : Nat → Prop) (Q : Nat → Val → Prop) :=
  Implementation (mkSpec P Q)

/-! ## Section 6: Combinators -/

/-- Convert the function argument to its string representation -/
def showArg {P : Nat → Prop} : Codable P (fun n res => res = Val.str (Nat.repr n)) :=
  { code := ⟨.toStr .arg⟩
    correct := fun _ _ => rfl }

/-- Convert a literal natural number to its string representation -/
def showNat {P : Nat → Prop} (m : Nat) : Codable P (fun _ res => res = Val.str (Nat.repr m)) :=
  { code := ⟨.toStr (.val (.nat m))⟩
    correct := fun _ _ => rfl }

/-- Return a string literal -/
def str {P : Nat → Prop} (s : String) : Codable P (fun _ res => res = Val.str s) :=
  { code := ⟨.val (.str s)⟩
    correct := fun _ _ => rfl }

/-- Helper lemma: evaluating append of two string-producing expressions -/
theorem eval_append_str {e1 e2 : Expr} {n : Nat} {s1 s2 : String}
    (h1 : e1.eval n = Val.str s1) (h2 : e2.eval n = Val.str s2) :
    (Expr.append e1 e2).eval n = Val.str (s1 ++ s2) := by
  simp only [Expr.eval, h1, h2]

/-- Concatenate two string-producing programs -/
def append {P : Nat → Prop} {x y : Nat → String}
    (r1 : Codable P (fun n res => res = Val.str (x n)))
    (r2 : Codable P (fun n res => res = Val.str (y n))) :
    Codable P (fun n res => res = Val.str (x n ++ y n)) :=
  { code := ⟨.append r1.code.body r2.code.body⟩
    correct := fun n hP =>
      have h1 : r1.code.body.eval n = Val.str (x n) := r1.correct n hP
      have h2 : r2.code.body.eval n = Val.str (y n) := r2.correct n hP
      eval_append_str h1 h2 }

/-! ## Section 7: Synthesis Tactic -/

/-- Tactic macro for synthesizing Codable programs -/
macro "vericode" : tactic =>
  `(tactic| repeat any_goals first | apply append | apply showArg | apply showNat | apply str)

/-! ## Section 8: Examples -/

/-- Convert the input to string and append "!" -/
def natToStringBang : Codable (fun _ => True) (fun n res => res = Val.str (Nat.repr n ++ "!")) := by
  vericode

-- Evaluate the synthesized program
#eval natToStringBang.code.eval 42
-- Val.str "42!"

-- Print the synthesized program
#eval natToStringBang.code.pretty
-- "fun n => toString(n) ++ \"!\""

/-- Always return "hello" regardless of input -/
def constHello : Codable (fun _ => True) (fun _ res => res = Val.str "hello") := by
  vericode

#eval constHello.code.eval 999
-- Val.str "hello"

#eval constHello.code.pretty
-- "fun n => \"hello\""

/-- Show the number twice with a separator -/
def showTwice : Codable (fun _ => True)
    (fun n res => res = Val.str (Nat.repr n ++ "," ++ Nat.repr n)) := by
  vericode

#eval showTwice.code.eval 7
-- Val.str "7,7"

#eval showTwice.code.pretty
-- "fun n => toString(n) ++ \",\" ++ toString(n)"

end Function
