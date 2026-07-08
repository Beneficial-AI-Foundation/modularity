import Loom.MonadAlgebras.WP.Basic

/-!
  Program Synthesis with Printable Programs

  We use a reified syntax that can be printed, rather than Lean functions.
  Stmt.eval maps directly to Id String.
-/

/-! ## Syntactic Program Representation -/

-- First-order expression language
inductive Expr where
  | var : String → Expr           -- variable reference
  | natLit : Nat → Expr           -- natural number literal
  | strLit : String → Expr        -- string literal
  | toStr : Expr → Expr           -- convert nat to string
  | append : Expr → Expr → Expr   -- string concatenation
  deriving Repr, BEq

-- Statement language (the synthesized programs)
inductive Stmt where
  | ret : Expr → Stmt                       -- return e
  | letBind : String → Expr → Stmt → Stmt   -- let x = e in s
  deriving Repr, BEq

/-! ## Pretty Printing -/

def Expr.pretty : Expr → String
  | .var x => x
  | .natLit n => s!"{n}"
  | .strLit s => s!"\"{s}\""
  | .toStr e => s!"toString({e.pretty})"
  | .append e1 e2 => s!"{e1.pretty} ++ {e2.pretty}"

def Stmt.pretty : Stmt → String
  | .ret e => s!"return {e.pretty}"
  | .letBind x e s => s!"let {x} = {e.pretty};\n{s.pretty}"

instance : ToString Expr := ⟨Expr.pretty⟩
instance : ToString Stmt := ⟨Stmt.pretty⟩

/-! ## Interpreter -/

-- Values in our language
inductive Val where
  | nat : Nat → Val
  | str : String → Val
  deriving Repr, BEq

-- Simple environment mapping variable names to values
abbrev Env := List (String × Val)

def Env.lookup (env : Env) (x : String) : Val :=
  env.find? (·.1 == x) |>.map (·.2) |>.getD (.nat 0)

-- Evaluate an expression to a value
def Expr.eval (env : Env) : Expr → Val
  | .var x => env.lookup x
  | .natLit n => .nat n
  | .strLit s => .str s
  | .toStr e => match e.eval env with
      | .nat n => .str (Nat.repr n)
      | .str s => .str s
  | .append e1 e2 => match e1.eval env, e2.eval env with
      | .str s1, .str s2 => .str (s1 ++ s2)
      | .str s1, .nat n2 => .str (s1 ++ Nat.repr n2)
      | .nat n1, .str s2 => .str (Nat.repr n1 ++ s2)
      | .nat n1, .nat n2 => .str (Nat.repr n1 ++ Nat.repr n2)

-- Evaluate a statement directly to Id String
def Stmt.eval (env : Env) : Stmt → Id String
  | .ret e => match e.eval env with
      | .str s => pure s
      | .nat n => pure (Nat.repr n)
  | .letBind x e s => s.eval ((x, e.eval env) :: env)

/-! ## Synthesis -/

-- Synthesize program for "n ↦ toString(n) ++ !"
def synthesizeNatToString (inputVar : String) : Stmt :=
  .letBind "s" (.toStr (.var inputVar)) (
  .letBind "result" (.append (.var "s") (.strLit "!")) (
  .ret (.var "result")))

/-! ## Correctness -/

def progCorrect (prog : Stmt) (n : Nat) (expected : String) : Prop :=
  prog.eval [("n", .nat n)] = expected

theorem synth_correct (n : Nat) :
    progCorrect (synthesizeNatToString "n") n (Nat.repr n ++ "!") := by
  simp only [progCorrect, synthesizeNatToString, Stmt.eval, Expr.eval, Env.lookup,
             List.find?, beq_self_eq_true, Option.map, Option.getD, pure]

/-! ## Demo -/

-- Print the synthesized program
#eval IO.println (synthesizeNatToString "n")

-- Run on concrete inputs
#eval (synthesizeNatToString "n").eval [("n", .nat 42)]   -- "42!"
#eval (synthesizeNatToString "n").eval [("n", .nat 100)]  -- "100!"
#eval (synthesizeNatToString "n").eval [("n", .nat 0)]    -- "0!"

/-! ## Triple -/

theorem interp_triple (n : Nat) :
    triple (m := Id) (l := Prop) True
      ((synthesizeNatToString "n").eval [("n", .nat n)])
      (fun res => res = Nat.repr n ++ "!") := by
  simp only [triple, wp, liftM, monadLift, MAlg.lift, Functor.map]
  simp only [synthesizeNatToString, Stmt.eval, Expr.eval, Env.lookup,
             List.find?, beq_self_eq_true, Option.map, Option.getD, pure]
  trivial
