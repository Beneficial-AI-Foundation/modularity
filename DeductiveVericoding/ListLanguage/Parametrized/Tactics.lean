import DeductiveVericoding.ListLanguage.Parametrized.Basic
import Lean

open Lean Elab Tactic Meta

namespace Parametrized

open ListLanguage

/- Here we have a collection of tactics, each of which should correspond roughly to one term in out programming language-/

/-- Closes the goal using the empty list -/
def NilPTactic {Γ : Ctx} (Cond : Env Tpe.denote Γ → List Nat → Prop) (h : ∀ env, Cond env []) : ImplP Γ .list Cond :=
  { code := .nil, correct := fun env => h env }

def NilPTactic' {Γ : Ctx} : ImplP Γ .list (fun _ out => out = []) :=
  { code := .nil, correct := fun _ => rfl}

/-- Relaxes the Condition to some globally weaker condition -/
def RelaxCondPTactic {Γ : Ctx} {t : Tpe} (Cond Cond' : Env Tpe.denote Γ → t.denote → Prop)
  (impl : ImplP Γ t Cond') (h : ∀ env, ∀ out,  Cond' env out → Cond env out) : ImplP Γ t Cond :=
  { code := impl.code, correct := fun env => h env _ (impl.correct env)}

/-- The `intro` step: from an implementation in the extended context `s :: Γ`, build one
    of arrow type in context `Γ`. The bound value `v` is prepended to the environment in
    the condition — this is the substitution of the introduced parameter. -/
def IntroPTactic (Γ : Ctx) (s t : Tpe) (Cond : Env Tpe.denote (s :: Γ) → t.denote → Prop)
    (impl : ImplP (s :: Γ) t Cond) :
    ImplP Γ (.arrow s t) (fun env f => ∀ v, Cond (v, env) (f v)) :=
  { code := .lam impl.code, correct := fun env v => impl.correct (v, env) }

/-- `introP` is a zero-argument front-end for `IntroPTactic`.

`IntroPTactic` forces the user to spell out the parameter type `s`, the result type `t`
and — the painful part — the *residual* condition `Cond`, because the higher-order
unification problem
```
(fun env f => ∀ v, ?Cond (v, env) (f v))  =?=  GoalCond
```
is outside Lean's pattern-unification fragment (`f v` is `?Cond` applied to a *non-variable*),
so `apply` cannot solve for `?Cond` on its own.

`introP` inspects the goal instead. It expects a goal `ImplP Γ (.arrow s t) GoalCond` where
`GoalCond = fun env f => ∀ v, body` and `f` occurs in `body` only as `f v`. It then builds
```
Cond := fun p out => body[  f v ↦ out,  v ↦ p.1,  env ↦ p.2  ]
```
and applies `IntroPTactic Γ s t Cond`. By construction, plugging this `Cond` back into
`fun env f => ∀ v, Cond (v, env) (f v)` β-reduces to `GoalCond`, so the `apply` closes the
head definitionally and leaves the single subgoal `ImplP (s :: Γ) t Cond`.

To keep the residual condition in the shape the other tactics (`ParPTactic`, …) expect, the
substitution is written in de Bruijn form rather than raw projections: the introduced value
becomes `env.getT 0 s`, and every pre-existing lookup `env.getT k u` is shifted to
`env.getT (k+1) u` (the parameter list just grew by one on the left). -/
elab "introP" : tactic => do
  let goal ← getMainGoal
  let tgt ← instantiateMVars (← whnf (← goal.getType))
  unless tgt.isAppOf ``ImplP do
    throwError "introP: goal is not `ImplP Γ t Cond`:{indentExpr tgt}"
  let #[Γ, T, goalCond] := tgt.getAppArgs
    | throwError "introP: malformed `ImplP` goal:{indentExpr tgt}"
  let Tw ← whnf T
  unless Tw.isAppOf ``Tpe.arrow do
    throwError "introP: the goal's type is not an arrow `.arrow s t`:{indentExpr Tw}"
  let #[s, t] := Tw.getAppArgs
    | throwError "introP: malformed arrow type:{indentExpr Tw}"
  -- Reconstruct the residual condition by "un-applying" the leading `∀ v` of `goalCond`.
  let cond ← lambdaTelescope goalCond fun binders body => do
    unless binders.size == 2 do
      throwError "introP: expected the goal condition to have the form `fun env f => …`"
    let env := binders[0]!
    let f := binders[1]!
    let body ← whnf body
    unless body.isForall do
      throwError "introP: the condition body must start with `∀ v, …`:{indentExpr body}"
    forallBoundedTelescope body (some 1) fun vs ib => do
      let v := vs[0]!
      let fv := mkApp f v
      let sΓ ← mkAppM ``List.cons #[s, Γ]
      let envTy ← mkAppM ``Env #[mkConst ``Tpe.denote, sΓ]
      let outTy := mkApp (mkConst ``Tpe.denote) t
      withLocalDeclD `env' envTy fun env' => do
      withLocalDeclD `out outTy fun out => do
        -- the introduced value, as a de Bruijn lookup in the extended environment
        let v0 ← mkAppM ``Env.getT #[env', mkNatLit 0, s]
        let ib := ib.replace fun e =>
          -- 1. `f v` is the output being described
          if e == fv then some out
          -- 2. shift a pre-existing lookup `env.getT k u` to `env'.getT (k+1) u`
          else if e.isAppOfArity ``Env.getT 4 && e.getAppArgs[1]! == env then
            let args := e.getAppArgs
            match args[2]!.nat? with
            | some k => some (mkAppN (mkConst ``Env.getT) #[sΓ, env', mkNatLit (k + 1), args[3]!])
            | none   => none
          -- 3. the introduced value `v`
          else if e == v then some v0
          else none
        -- the old environment must only survive inside shifted `getT`s
        if ib.containsFVar env.fvarId! then
          throwError "introP: the condition mentions the environment outside of `env.getT`; \
            cannot infer the residual condition automatically"
        mkLambdaFVars #[env', out] ib
  let e := mkAppN (mkConst ``IntroPTactic) #[Γ, s, t, cond]
  liftMetaTactic fun g => g.apply e

def ParPTactic (Γ : Ctx) (t : Tpe) (n : Nat) :
    ImplP Γ t (fun env out => out = env.getT n t) :=
  { code := .par n t, correct := fun _ => rfl}

def ConsPTactic (Γ : Ctx) (x : Env Tpe.denote Γ →  Nat) (xs : Env Tpe.denote Γ → List Nat)
  (impl1 : ImplP Γ .nat (fun env out => out = x env))
  (impl2 : ImplP Γ .list (fun env out => out = xs env)) :
    ImplP Γ .list (fun env out => out = x env :: xs env) :=
  { code := .cons impl1.code impl2.code
    correct := fun env => by simp [Trm.eval, impl1.correct env, impl2.correct env] }

/-- **Applied `listRec` combinator.** Folds `target` under an invariant `Inv` (which may
    read the ambient parameters `Γ`). On `a :: l` the `step` runs in the context extended
    with the head `a` (`.par 0`), the tail `l` (`.par 1`) and the recursive result `res`
    (`.par 2`), and must turn `Inv l res` into `Inv (a :: l) out`. Produces a `.list`. -/
def ListRecPTactic (Γ : Ctx) (Inv : Env Tpe.denote Γ → List Nat → List Nat → Prop)
    (base : ImplP Γ .list (fun env out => Inv env [] out))
    (step : ImplP (.nat :: .list :: .list :: Γ) .list (fun ⟨a, l, res, env⟩ out => Inv env l res → Inv env (a :: l) out)) :
    ImplP Γ (.arrow .list .list) (fun env f => ∀ l, Inv env l (f l)) :=
  { code := .listRec base.code step.code
    correct := fun env l => by
      simp only [Trm.eval]
      induction l with
      | nil => exact base.correct env
      | cons a l ih => exact step.correct (a, (l, (_, env))) ih}

def AppPTactic (Γ : Ctx) (s t : Tpe) (target : Env Tpe.denote Γ → s.denote) (Cond : Env Tpe.denote Γ → s.denote → t.denote → Prop)
  (base : ImplP Γ s (fun env out => out = target env))
  (step : ImplP Γ (.arrow s t) (fun env f => ∀ x, Cond env x (f x))) :
    ImplP Γ t (fun env out => Cond env (target env) out) :=
  { code := .app step.code base.code, correct env := by
      rw [Trm.eval, base.correct]
      exact step.correct env (target env)
  }
