import DeductiveVericoding.ListLanguage.Parametrized.Basic

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
