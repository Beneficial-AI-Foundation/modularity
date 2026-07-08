import Loom.MonadAlgebras.WP.Basic

/-!
  Program Synthesis with Printable Programs

  We use a reified syntax (Stmt) that can be printed.
  StmtM is a monad that mirrors the structure of Stmt.
  Stmt.evalM maps Stmt to StmtM Val.
-/

/-! ## Syntactic Program Representation -/

inductive Expr where
  | var : String → Expr
  | natLit : Nat → Expr
  | strLit : String → Expr
  | toStr : Expr → Expr
  | append : Expr → Expr → Expr
  deriving Repr, BEq

inductive Stmt where
  | ret : Expr → Stmt
  | letBind : String → Expr → Stmt → Stmt
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

/-! ## Values and Environment -/

inductive Val where
  | nat : Nat → Val
  | str : String → Val
  deriving Repr, BEq

abbrev Env := List (String × Val)

/-! ## StmtM: A Monad mirroring Stmt structure -/

-- StmtM is a reader monad over the environment
-- This mirrors how Stmt evaluates: it reads variables from an environment
abbrev StmtM := ReaderT Env Id

/-! ## Stmt Evaluation in StmtM -/

def StmtM.readVar (x : String) : StmtM Val :=
  fun env => env.find? (·.1 == x) |>.map (·.2) |>.getD (.nat 0)

def StmtM.withVar (x : String) (v : Val) (m : StmtM α) : StmtM α :=
  fun env => m ((x, v) :: env)

def Expr.evalM : Expr → StmtM Val
  | .var x => StmtM.readVar x
  | .natLit n => pure (.nat n)
  | .strLit s => pure (.str s)
  | .toStr e => do
      match ← e.evalM with
      | .nat n => pure (.str (Nat.repr n))
      | .str s => pure (.str s)
  | .append e1 e2 => do
      let v1 ← e1.evalM
      let v2 ← e2.evalM
      match v1, v2 with
      | .str s1, .str s2 => pure (.str (s1 ++ s2))
      | .str s1, .nat n2 => pure (.str (s1 ++ Nat.repr n2))
      | .nat n1, .str s2 => pure (.str (Nat.repr n1 ++ s2))
      | .nat n1, .nat n2 => pure (.str (Nat.repr n1 ++ Nat.repr n2))

def Stmt.evalM : Stmt → StmtM Val
  | .ret e => e.evalM
  | .letBind x e s => do
      let v ← e.evalM
      StmtM.withVar x v s.evalM

/-! ## Running StmtM -/

def StmtM.run (m : StmtM α) (env : Env) : Id α := m env

/-! ## Correctness Example -/

def natToStringBang (inputVar : String) : Stmt :=
  .letBind "s" (.toStr (.var inputVar)) (
  .letBind "result" (.append (.var "s") (.strLit "!")) (
  .ret (.var "result")))

theorem natToStringBang_correct (n : Nat) :
    (natToStringBang "n").evalM.run [("n", .nat n)] = (.str (Nat.repr n ++ "!")) := by
  simp only [natToStringBang, Stmt.evalM, Expr.evalM, StmtM.run]
  rfl

theorem interp_triple (n : Nat) :
    triple (m := Id) (l := Prop) True
      ((natToStringBang "n").evalM.run [("n", .nat n)])
      (fun res => res = .str (Nat.repr n ++ "!")) := by
  simp only [triple, wp, natToStringBang, Stmt.evalM, Expr.evalM, StmtM.run,
             StmtM.withVar, StmtM.readVar, bind, ReaderT.bind, pure, ReaderT.pure,
             liftM, monadLift, MAlg.lift, Functor.map,
             List.find?, beq_self_eq_true, Option.map, Option.getD]
  trivial

/-! ## TripleStmt -/

-- tripleStmt is like triple, but for syntactic programs (Stmt)
-- P and Q are now functions of the environment, matching the reader monad structure
def tripleStmt (P : Env → Prop) (s : Stmt) (Q : Val → Env → Prop) : Prop :=
  triple (m := StmtM) (l := Env → Prop) P s.evalM Q

-- Helper to lookup a string value from the environment
def Env.lookupStr (env : Env) (name : String) : Option String :=
  match env.find? (·.1 == name) with
  | some (_, .str s) => some s
  | _ => none

-- Helper to lookup a nat value from the environment
def Env.lookupNat (env : Env) (name : String) : Option Nat :=
  match env.find? (·.1 == name) with
  | some (_, .nat n) => some n
  | _ => none

/-! ## Refined Stmt: Existential form with extractable program -/

/-- A statement refined by its correctness proof -/
structure RefinedStmt (P : Env → Prop) (Q : Val → Env → Prop) where
  stmt : Stmt
  correctness : tripleStmt P stmt Q

/-! ## append refined statement -/

theorem append_correct (varName : String) (suffix : String) :
    tripleStmt
      (fun env => (env.lookupStr varName).isSome)
      (.ret (.append (.var varName) (.strLit suffix)))
      (fun res env => ∀ input, env.lookupStr varName = some input → res = .str (input ++ suffix)) := by
  simp only [tripleStmt, triple, wp, Stmt.evalM, Expr.evalM, Env.lookupStr]
  intro env henv input hinput
  simp only [StmtM.readVar, bind, ReaderT.bind, pure, ReaderT.pure] at *
  split at henv <;> simp_all [ReaderT.pure, Pure.pure]

/-- Derive a refined statement that appends suffix to a variable -/
def append_refined (varName : String) (suffix : String) :
    RefinedStmt
      (fun env => (env.lookupStr varName).isSome)
      (fun res env => ∀ input, env.lookupStr varName = some input → res = .str (input ++ suffix)) :=
  { stmt := .ret (.append (.var varName) (.strLit suffix))
    correctness := append_correct varName suffix }

-- Derive a stmt that appends "!" to a string using RefinedStmt
def appendBang :
    RefinedStmt
      (fun env => (env.lookupStr "input").isSome)
      (fun res env => ∀ input, env.lookupStr "input" = some input → res = .str (input ++ "!")) := by
  exact append_refined "input" "!"

-- Extract and print the derived statement
#eval IO.println appendBang.stmt

-- We can also verify it computes correctly
#eval appendBang.stmt.evalM.run [("input", .str "hello")]

/-! ## toStr refined statement -/

theorem toStr_correct (varName : String) :
    tripleStmt
      (fun env => (env.lookupNat varName).isSome)
      (.ret (.toStr (.var varName)))
      (fun res env => ∀ n, env.lookupNat varName = some n → res = .str (Nat.repr n)) := by
  simp only [tripleStmt, triple, wp, Stmt.evalM, Expr.evalM, Env.lookupNat]
  intro env henv n hn
  simp only [StmtM.readVar, bind, ReaderT.bind, pure] at *
  split at henv <;> simp_all [ReaderT.pure, Pure.pure]

def toStr_refined (varName : String) :
    RefinedStmt
      (fun env => (env.lookupNat varName).isSome)
      (fun res env => ∀ n, env.lookupNat varName = some n → res = .str (Nat.repr n)) :=
  { stmt := .ret (.toStr (.var varName))
    correctness := toStr_correct varName }

/-! ## letBind refined statement combinator -/

/-- Sequential composition: letBind with an expression and a body statement.
    The postcondition relates the result to the extended environment. -/
theorem letBind_correct (varName : String) (e : Expr) (body : Stmt)
    (P : Env → Prop) (R : Val → Env → Prop)
    (hbody : ∀ v env, P env → e.evalM env = v →
             tripleStmt (fun env' => env' = (varName, v) :: env) body
                        (fun res _ => R res env)) :
    tripleStmt P (.letBind varName e body) R := by
  simp only [tripleStmt, triple, wp, Stmt.evalM]
  intro env hP
  have hb := hbody (e.evalM env) env hP rfl
  simp only [tripleStmt, triple, wp] at hb
  exact hb _ rfl

/-- Simpler letBind: the body's precondition just needs the variable to exist -/
theorem letBind_simple (varName : String) (e : Expr) (body : Stmt)
    (Q : Val → Env → Prop)
    (hbody : tripleStmt (fun env => (env.find? (·.1 == varName)).isSome) body Q) :
    tripleStmt (fun _ => True)
               (.letBind varName e body)
               (fun res env => Q res ((varName, e.evalM env) :: env)) := by
  simp only [tripleStmt, triple, wp, Stmt.evalM]
  intro env _
  have h := hbody
  simp only [tripleStmt, triple, wp] at h
  apply h
  simp [List.find?]

/-- Refined letBind combinator -/
def letBind_refined (varName : String) (e : Expr)
    (bodyRef : RefinedStmt
                 (fun env => (env.find? (·.1 == varName)).isSome)
                 Q) :
    RefinedStmt
      (fun _ => True)
      (fun res env => Q res ((varName, e.evalM env) :: env)) :=
  { stmt := .letBind varName e bodyRef.stmt
    correctness := letBind_simple varName e bodyRef.stmt Q bodyRef.correctness }

/-! ## Deriving natToStringBang using tactics -/

/-- interp_triple expressed as a RefinedStmt -/
def natToStringBang_refined :
    RefinedStmt
      (fun env => (env.lookupNat "n").isSome)
      (fun res env => ∀ n, env.lookupNat "n" = some n → res = .str (Nat.repr n ++ "!")) := by
  -- Goal: construct a RefinedStmt
  -- We need to provide both a stmt and a proof of its correctness
  constructor
  -- stmt goal
  · sorry
  -- correctness goal
  · sorry
