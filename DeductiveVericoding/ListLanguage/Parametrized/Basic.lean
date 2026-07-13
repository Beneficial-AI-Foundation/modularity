import DeductiveVericoding.ListLanguage.Basic

open ListLanguage

namespace Parametrized

/-! # Parametrized terms (full de Bruijn) + translation to `ListLanguage`

A self-contained, intrinsically-typed language whose terms carry a heterogeneous
parameter context `Γ : List Tpe`. There is a *single* binding discipline: `.lam`
extends the context and `.par i` is the (well-typed) de Bruijn access. No PHOAS `rep`.

`ImplP Γ t Cond` is the parametrized "Problem/solution": a term of type `t` in context
`Γ`, verified against one condition `Cond : Env Γ → t.denote → Prop` (parameter
environment → output). `IntroP` introduces a parameter, substituting the bound value
into the condition.

Everything lives here, importing only `Basic`. `toImpl` translates a solved
`ImplP [] (inTpe ⟶ outTpe) …` back into a genuine `ListLanguage.Impl`, so a Problem
can be *stated* in `ListLanguage` and *solved* in this language. -/

/-- A typing context: the parameter types in scope. -/
abbrev Ctx := List Tpe

/-- Intrinsically-typed de Bruijn terms of type `t` in context `Γ`. -/
inductive Trm : Ctx → Tpe → Type where
  | unit    : {Γ : Ctx} → Trm Γ .unit
  | nil     : {Γ : Ctx} → Trm Γ .list
  | num     : {Γ : Ctx} → Nat → Trm Γ .nat
  | par     : {Γ : Ctx} → (i : Nat) → (t : Tpe) → Trm Γ t
  | cons    : {Γ : Ctx} → Trm Γ .nat → Trm Γ .list → Trm Γ .list
  | mkPair  : {Γ : Ctx} → {t u : Tpe} → Trm Γ t → Trm Γ u → Trm Γ (.pair t u)
  | fst     : {Γ : Ctx} → {t u : Tpe} → Trm Γ (.pair t u) → Trm Γ t
  | snd     : {Γ : Ctx} → {t u : Tpe} → Trm Γ (.pair t u) → Trm Γ u
  | lam     : {Γ : Ctx} → {s u : Tpe} → Trm (s :: Γ) u → Trm Γ (.arrow s u)
  | app     : {Γ : Ctx} → {s u : Tpe} → Trm Γ (.arrow s u) → Trm Γ s → Trm Γ u
  /-- Applied list recursion producing a `.list`. On `a :: l` the `step` runs in the
      context extended with `a` (`.par 0`), `l` (`.par 1`) and the recursive result on `l`
      (`.par 2`); on `[]` it is `base`. The last argument is the list being folded. -/
  | listRec : {Γ : Ctx} → Trm Γ .list → Trm (.nat :: .list :: .list :: Γ) .list → Trm Γ (.arrow .list .list)
  | true    : {Γ : Ctx} → Trm Γ .bool
  | false   : {Γ : Ctx} → Trm Γ .bool
  | le      : {Γ : Ctx} → Trm Γ .nat → Trm Γ .nat → Trm Γ .bool
  | ite     : {Γ : Ctx} → {t : Tpe} → Trm Γ .bool → Trm Γ t → Trm Γ t → Trm Γ t

/-- Environment over a value representation `rep`, matching a context. -/
def Env (rep : Tpe → Type) : Ctx → Type
  | [] => Unit
  | t :: ts => rep t × Env rep ts

/-- Look up the `i`-th value in a `Tpe.denote` environment (for evaluation). -/
def Env.get : {Γ : Ctx} → Env Tpe.denote Γ → (i : Nat) → (Γ.getD i .unit).denote
  | [], _, _ => ()
  | _ :: _, (v, _), 0 => v
  | _ :: _, (_, e), i + 1 => Env.get e i

def Env.getT {Γ : Ctx} (env : Env Tpe.denote Γ) (i : Nat) (t : Tpe) : t.denote :=
  if h : (Γ.getD i .unit) = t then h ▸ env.get i else default

/-- The list-recursion scheme used by `.listRec`: on `a :: l` the step `s` receives the
    head `a`, the tail `l`, and the recursive result on `l`. Named (not a `let rec`) so it
    has clean equation lemmas for reasoning. -/
def listFold (b : List Nat) (s : Nat → List Nat → List Nat → List Nat) : List Nat → List Nat
  | [] => b
  | a :: l => s a l (listFold b s l)

/-- Evaluation under a matching environment. -/
def Trm.eval : {Γ : Ctx} → {t : Tpe} → Trm Γ t → Env Tpe.denote Γ → t.denote
  | _, _, .unit, _ => ()
  | _, _, .nil, _ => []
  | _, _, .num n, _ => n
  | _, _, .par i s, env => env.getT i s
  | _, _, .cons h t, env => h.eval env :: t.eval env
  | _, _, .mkPair a b, env => (a.eval env, b.eval env)
  | _, _, .fst e, env => (e.eval env).1
  | _, _, .snd e, env => (e.eval env).2
  | _, _, .lam body, env => fun v => body.eval (v, env)
  | _, _, .app f a, env => (f.eval env) (a.eval env)
  | _, _, .listRec base step, env => listFold (base.eval env) (fun a l res => step.eval (a, (l, (res, env))))
  | _, _, (true), _ => Bool.true
  | _, _, (false), _ => Bool.false
  | _, _, (le e1 e2), env => Nat.ble (e1.eval env) (e2.eval env)
  | _, _, (ite c t e), env => bif c.eval env then t.eval env else e.eval env

/-- A parametrized implemeåntation: a term of type `t` in context `Γ`, verified against a
    single condition relating the parameter environment to the output. -/
structure ImplP (Γ : Ctx) (t : Tpe) (Cond : Env Tpe.denote Γ → t.denote → Prop) where
  code : Trm Γ t
  correct : ∀ env, Cond env (code.eval env)
