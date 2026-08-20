import DeductiveVericoding.ListLanguage.Basic
import DeductiveVericoding.ListLanguage.VericodeRuleSet
import Lean
import Aesop

/- # TACTICS : Here we have a collection of vericoding tactics-/

open ListLanguage
open Lean Elab Tactic Meta

/- The following are tactics for immediately closing the goal-/

def NilTactic {t : Tpe} {Pre : t.denote → Prop} : Impl t .list Pre (fun _ out => out = []) :=
  { code := .lam fun _ => .nil, correct _ _ := rfl}

def UnitTactic {t : Tpe} {Pre : t.denote → Prop} : Impl t .unit Pre (fun _ out => out = ()) :=
  { code := .lam fun _ => .unit, correct _ _ := rfl}

def TrueTactic {t : Tpe} {Pre : t.denote → Prop} : Impl t .bool Pre (fun _ out => out = true) :=
  { code := .lam fun _ => .true, correct _ _ := rfl}

def FalseTactic {t : Tpe} {Pre : t.denote → Prop} : Impl t .bool Pre (fun _ out => out = false) :=
  { code := .lam fun _ => .false, correct _ _ := rfl}

def NumTactic {t : Tpe} {Pre : t.denote → Prop} (n : Nat) : Impl t .nat Pre (fun _ out => out = n) :=
  { code := .lam fun _ => .num n, correct _ _ := rfl}

def IdentityTactic {t : Tpe} {Pre : t.denote → Prop} : Impl t t Pre (fun inp out => out = inp) :=
  { code := .lam fun k => .var k, correct _ _ := rfl}

/- The following are tactics stripping a function application -/

def FstTactic {s t u : Tpe} {Pre : s.denote → Prop} (target : s.denote → t.denote × u.denote)
  (impl : Impl s (.pair t u) Pre (fun inp out => out = target inp)) :
    Impl s t Pre (fun inp out => out = (target inp).1) :=
  { code := .lam fun k => .fst (.app impl.code (.var k))
    correct inp pre := by
      simp [Trm.eval, Trm'.eval]
      congr
      exact impl.correct inp pre
  }

def SndTactic {s t u : Tpe} {Pre : s.denote → Prop} (target : s.denote → t.denote × u.denote)
  (impl : Impl s (.pair t u) Pre (fun inp out => out = target inp)) :
    Impl s u Pre (fun inp out => out = (target inp).2) :=
  { code := .lam fun k => .snd (.app impl.code (.var k))
    correct inp pre := by
      simp [Trm.eval, Trm'.eval]
      congr
      exact impl.correct inp pre
  }

def PairTactic {s t u : Tpe} {Pre : s.denote → Prop} (target1 : s.denote → t.denote) (target2 : s.denote → u.denote)
  (impl1 : Impl s t Pre (fun inp out => out = target1 inp))
  (impl2 : Impl s u Pre (fun inp out => out = target2 inp)) :
    Impl s (.pair t u) Pre (fun inp out => out = (target1 inp, target2 inp)) :=
  { code := .lam fun k => .mkPair (.app impl1.code (.var k)) (.app impl2.code (.var k))
    correct inp pre := by
      simp [Trm.eval, Trm'.eval]
      congr
      · exact impl1.correct inp pre
      exact impl2.correct inp pre
  }

def ConsTactic {t : Tpe} {Pre : t.denote → Prop}
  (target1 : t.denote → Nat) (target2 : t.denote → List Nat)
  (impl1 : Impl t .nat Pre (fun inp out => out = target1 inp))
  (impl2 : Impl t .list Pre (fun inp out => out = target2 inp)) :
    Impl t .list Pre (fun inp out => out = target1 inp :: target2 inp) :=
  { code := .lam fun k => .cons (.app impl1.code (.var k)) (.app impl2.code (.var k))
    correct inp pre := by
      simp [Trm.eval, Trm'.eval]
      congr
      · exact impl1.correct inp pre
      exact impl2.correct inp pre
  }

def LETactic {t : Tpe} {Pre : t.denote → Prop}
  (target1 : t.denote → Nat) (target2 : t.denote → Nat)
  (impl1 : Impl t .nat Pre (fun inp out => out = target1 inp))
  (impl2 : Impl t .nat Pre (fun inp out => out = target2 inp)) :
    Impl t .bool Pre (fun inp out => out = Nat.ble (target1 inp) (target2 inp)) :=
  { code := .lam fun k => .le (.app impl1.code (.var k)) (.app impl2.code (.var k))
    correct inp pre := by
      simp [Trm.eval, Trm'.eval]
      congr
      · exact impl1.correct inp pre
      exact impl2.correct inp pre
  }

/- The following are tactics that make some kind of choice, their application is less straightforward -/

/- Split the goal into two cases, similar to by_cases in Lean -/
def CasesTactic {s t : Tpe} {Pre : s.denote → Prop} {Post : s.denote → t.denote → Prop} (cond : s.denote → Bool)
  (implCond : Impl s .bool Pre (fun inp out => out = cond inp))
  (implThen : Impl s t (fun inp => Pre inp ∧ cond inp) Post)
  (implElse : Impl s t (fun inp => Pre inp ∧ ¬ cond inp) Post) :
    Impl s t Pre (fun inp out => Post inp out) :=
  {
    code := .lam fun k => .ite (.app implCond.code (.var k)) (.app implThen.code (.var k)) (.app implElse.code (.var k))
    correct inp pre := by
      have hc : implCond.code.eval inp = cond inp := implCond.correct inp pre
      by_cases hcond : cond inp
      · simp [Trm.eval, Trm'.eval, hc, hcond]
        exact implThen.correct inp ⟨pre, hcond⟩
      simp [Trm.eval, Trm'.eval, hc, hcond]
      exact implElse.correct inp ⟨pre, hcond⟩
  }

/- This Tactic picks a specific implementation that satisfies the Post Condition and leaves a proof obligation-/
def UseTactic {s t : Tpe} {Pre : s.denote → Prop} {Post : s.denote → t.denote → Prop}
  (target : s.denote → t.denote)
  (impl : Impl s t Pre (fun inp out => out = target inp))
  (h : ∀ inp, Pre inp → Post inp (target inp)) :
    Impl s t Pre Post :=
  { code := impl.code
    correct inp pre := by
      have : impl.code.eval inp = target inp := impl.correct inp pre
      simp [Trm.eval, this, h inp pre]
  }

/- Build `Impl s u` by chaining `Impl s t` and `Impl t u`, maybe this can be scrapped  -/
def SplitTactic (s t u : Tpe) {Pre : s.denote → Prop} (target : s.denote → t.denote) (Post : t.denote → u.denote → Prop)
  (base : Impl s t Pre (fun inp out => out = target inp))
  (step : Impl t u (fun inp => ∃ s, Pre s ∧ inp = target s) Post) :
    Impl s u Pre (fun inp out => Post (target inp) out) :=
  { code := .lam fun k => .app step.code (.app base.code (.var k))
    correct inp pre := by
      have : base.code.eval inp = target inp := base.correct inp pre
      simp [Trm.eval, Trm'.eval, this]
      exact step.correct (target inp) ⟨inp, pre, rfl⟩
  }

/-  Version of SplitTactic without the precondition on the step case. -/
def SplitTactic' (s t u : Tpe) {Pre : s.denote → Prop} (target : s.denote → t.denote) (Post : t.denote → u.denote → Prop)
  (base : Impl s t Pre (fun inp out => out = target inp))
  (step : Impl t u (fun _ => True) Post) :
    Impl s u Pre (fun inp out => Post (target inp) out) :=
  { code := .lam fun k => .app step.code (.app base.code (.var k))
    correct inp pre := by
      have : base.code.eval inp = target inp := base.correct inp pre
      simp [Trm.eval, Trm'.eval, this]
      exact step.correct (target inp) trivial
  }

def ListRecTactic {t : Tpe} {Pre : t.denote × List Nat → Prop} {Post : t.denote × List Nat → List Nat → Prop}
  (hpre : ∀ p, ∀ a, ∀ l, Pre (p, a :: l) → Pre (p, l))
  (base : Impl t .list (fun inp ↦ Pre (inp, [])) (fun p out ↦ Post (p, []) out))
  (step : Impl (.pair t (.pair .nat (.pair .list .list))) .list (fun (p, (a, (l, res))) ↦ Pre (p, a :: l) ∧  Post (p, l) res) (fun (p, (a, (l, _))) out ↦ Post (p, (a :: l)) out)) :
    Impl (.pair t .list) .list Pre Post :=
  { code := .listRec base.code step.code
    correct inp pre := by
      obtain ⟨par, l⟩ := inp
      induction l with
      | nil => exact base.correct par pre
      | cons a l ih => exact step.correct ⟨par, ⟨a, ⟨l, _⟩⟩⟩ ⟨pre, (ih (hpre _ _ _ pre))⟩
  }

--version without the parameter t
def ListRecTactic' {Post : List Nat → List Nat → Prop}
  (base : Impl .unit .list (fun _ ↦ True) (fun _ out ↦ Post [] out))
  (step : Impl (.pair .nat (.pair .list .list)) .list (fun (_, (l, res)) ↦ Post l res) (fun (a, (l, _)) out ↦ Post (a :: l) out)) :
    Impl .list .list (fun _ ↦ True) Post :=
  {
    code := .lam fun k => .app (.listRec base.code (.lam fun l => .app step.code (.snd (.var l)))) (.mkPair .unit (.var k))
    correct inp _ := by
      induction inp with
      | nil => exact base.correct _ (by trivial)
      | cons a l ih => exact step.correct ⟨a, ⟨l, _⟩⟩ ih
  }

/-- **Applied helper.** Build `Impl I t Pre (fun inp out => Cond inp (arg inp) out)` by
    applying a helper function `step : I → (s → t)` to the argument `arg inp. -/
def AppTactic (I s t : Tpe) (Pre : I.denote → Prop) (arg : I.denote → s.denote)
    (Cond : I.denote → s.denote → t.denote → Prop)
    (argImpl : Impl I s Pre (fun inp out => out = arg inp))
    (fnImpl : Impl I (.arrow s t) (fun _ => True) (fun inp f => ∀ x, Cond inp x (f x))) :
    Impl I t Pre (fun inp out => Cond inp (arg inp) out) :=
  { code := .lam fun k => .app (.app fnImpl.code (.var k)) (.app argImpl.code (.var k))
    correct inp pre := by
      have hb : argImpl.code.eval inp = arg inp := argImpl.correct inp pre
      show Cond inp (arg inp) (fnImpl.code.eval inp (argImpl.code.eval inp))
      rw [hb]
      exact fnImpl.correct inp trivial (arg inp)
  }

/-- **Introduce the argument of a helper.** Turn a solved `Impl (.pair I s) t` (with the new
    argument paired onto the input) into an arrow-valued `Impl I (.arrow s t)`. The dual of
    `AppTactic`. -/
def IntroTactic (I s t : Tpe) (Pre : I.denote → Prop) (PairPost : (I.denote × s.denote) → t.denote → Prop)
    (impl : Impl (.pair I s) t (fun p => Pre p.1) PairPost) :
    Impl I (.arrow s t) Pre (fun inp f => ∀ x, PairPost (inp, x) (f x)) :=
  { code := .lam fun k => .lam fun x => .app impl.code (.mkPair (.var k) (.var x))
    correct inp pre := by
      intro x
      show PairPost (inp, x) (impl.code.eval (inp, x))
      exact impl.correct (inp, x) pre
  }

/-- Relax the postcondition to a globally-stronger one `Post'` (which may exploit the
    precondition `Pre`). The implementation is reused verbatim; only the specification is
    weakened. -/
def RelaxPostTactic {I O : Tpe} {Pre : I.denote → Prop} (Post Post' : I.denote → O.denote → Prop)
    (impl : Impl I O Pre Post')
    (h : ∀ inp, Pre inp → ∀ out, Post' inp out → Post inp out) :
    Impl I O Pre Post :=
  { code := impl.code
    correct := fun inp hpre => h inp hpre _ (impl.correct inp hpre) }

def RelaxPreTactic {I O : Tpe} {Pre : I.denote → Prop} {Post : I.denote → O.denote → Prop} (Pre' : I.denote → Prop)
    (impl : Impl I O Pre' Post)
    (h : ∀ inp, Pre inp → Pre' inp) :
    Impl I O Pre Post :=
  { code := impl.code
    correct := fun inp hpre => impl.correct inp (h inp hpre) }

/-- Decode an input `Tpe` built from right-nested `.pair`s into its leaf components,
    e.g. `pair a (pair b c) ↦ #[a, b, c]`. Matches how anonymous-constructor patterns
    `fun (x, y, z) => …` destructure a nested product. -/
partial def decodeInputTpe (I : Expr) : Array Expr :=
  if I.isAppOfArity ``Tpe.pair 2 then
    #[I.getAppArgs[0]!] ++ decodeInputTpe I.getAppArgs[1]!
  else #[I]

/-- Build a right-nested tuple `⟨x₀, x₁, …⟩` from component values. -/
partial def mkNestedTuple (xs : Array Expr) : MetaM Expr := do
  if xs.size ≤ 1 then
    pure xs[0]!
  else
    let rest ← mkNestedTuple (xs.extract 1 xs.size)
    mkAppM ``Prod.mk #[xs[0]!, rest]

/-- `pushpre` closes the "precondition is an equality" shape that a `listRec` step goal takes
    after `simp`:
```
Impl I O (fun inp => x = s) (fun inp out => … s …)
```
where the precondition `Pre inp` reduces to an equality `x = s` (typically `x` is the
recursive result and `s` the term it stands for), and `s` also occurs in the postcondition.
`pushpre` rewrites the postcondition by replacing every occurrence of `s` with `x`, i.e.
relaxes to `Post' := fun inp out => (… s …)[s ↦ x]`, and applies `RelaxPostTactic`, discharging
the side goal `∀ inp, Pre inp → ∀ out, Post' inp out → Post inp out` automatically. Only the
implementation subgoal `Impl I O Pre Post'` remains. -/
elab "pushpre" : tactic => do
  let goals ← getGoals
  if goals.isEmpty then throwError "pushpre: no goals"
  let goal := goals.head!
  let restGoals := goals.tail!
  let tgt ← instantiateMVars (← whnf (← goal.getType))
  unless tgt.isAppOf ``Impl do
    throwError "pushpre: goal is not `Impl I O Pre Post`:{indentExpr tgt}"
  let #[I, O, Pre, Post] := tgt.getAppArgs
    | throwError "pushpre: malformed `Impl` goal:{indentExpr tgt}"
  let comps := decodeInputTpe I
  let m := comps.size
  let denote (t : Expr) : Expr := mkApp (mkConst ``Tpe.denote) t
  let decls := comps.map fun t => (`c, fun (_ : Array Expr) => pure (denote t))
  -- Build the relaxed postcondition `Post'` by reducing the pattern matches on a fresh
  -- constructor tuple, then re-expressing everything via projections of a packed input.
  let post' ← withLocalDeclsD decls fun cs => do
    let tuple ← mkNestedTuple cs
    let preBody ← whnf (mkApp Pre tuple)
    unless preBody.isAppOfArity ``Eq 3 do
      throwError "pushpre: precondition does not reduce to an equality `x = s`:{indentExpr preBody}"
    let x := preBody.getAppArgs[1]!
    let s := preBody.getAppArgs[2]!
    withLocalDeclD `out (denote O) fun out => do
      let postBody ← whnf (mkAppN Post #[tuple, out])
      unless (postBody.find? (· == s)).isSome do
        throwError "pushpre: the precondition's RHS does not occur in the postcondition"
      let newBody := postBody.replace fun e => if e == s then some x else none
      withLocalDeclD `inp (denote I) fun inp => do
        let mut projs := #[]
        let mut acc := inp
        for i in [0:m] do
          if i + 1 == m then
            projs := projs.push acc
          else
            projs := projs.push (← mkAppM ``Prod.fst #[acc])
            acc ← mkAppM ``Prod.snd #[acc]
        let newBody' := newBody.replaceFVars cs projs
        mkLambdaFVars #[inp, out] newBody'
  let e := mkAppN (mkConst ``RelaxPostTactic) #[I, O, Pre, Post, post']
  let gs ← goal.apply e
  let mut implGoals := #[]
  for g in gs do
    if ← g.withContext do return (← whnf (← g.getType)).isAppOf ``Impl then
      implGoals := implGoals.push g
    else
      -- discharge `∀ inp, Pre inp → ∀ out, Post' inp out → Post inp out`
      setGoals [g]
      let ids ← (Array.range m).mapM fun i =>
        `(rcasesPat| $(mkIdent (Name.mkSimple s!"y{i}")):ident)
      evalTactic (← `(tactic|
        intro pinp phpre pout phpost <;>
        obtain ⟨$ids,*⟩ := pinp <;>
        rw [phpre] at phpost <;>
        exact phpost))
  setGoals (implGoals.toList ++ restGoals)

/-! # THE `vericode` TACTIC

`vericode` is a backtracking tree search over the vericoding combinators, implemented on top
of aesop's `VericodeL` rule set`.

The value-producing combinators (`ConsTactic`, `ListRecTactic`, `NumTactic`, …) recover their
higher-order arguments — the `target`s and the `Post` invariant — by ordinary congruence
during `apply`, so they need no custom front-ends (à la `introP`/`listRecP`): they are plain
`apply` rules. They run at **`default` transparency** so that a postcondition presented as a
*match* (from an anonymous-constructor lambda `fun ⟨x, xs⟩ out => …`) reduces via structure-eta
and the `target` metavariables get solved.

Two things get special handling:
* **projections.** `FstTactic`/`SndTactic` each leave the *discarded* component's type as a
  metavariable, resolved only by a later `IdentityTactic`; aesop reconstructs the proof across
  that shared metavariable and fills it with `sorry`. So projection goals are closed instead by
  `projClose`, a front-end that builds the *entire* `.fst`/`.snd`/`.var` term at once — a fully
  concrete term with no metavariables for aesop to mishandle.
* **`pushpre`** is an elaborator, wrapped as a `tactic` rule.

Rule phases:
* **goal closers are `safe`** (`NilTactic`, `UnitTactic`, `TrueTactic`, `FalseTactic`,
  `NumTactic`, and `projClose`): each fully closes a goal, so committing is never a mistake.
* **recursion (`ListRecTactic`, `ListRecTactic'`) is `unsafe 90%`** — preferred, backtrackable.
* **`ConsTactic` is `unsafe 70%`**.
* **`pushpre` is `unsafe 95%` `tactic`**: aesop's norm phase runs `simp` first, exposing the
  `Pre → Post` shape it consumes (mirroring the manual `simp; pushpre` idiom). On non-step
  goals it just fails and the search moves on.
* **`relaxPost` is `unsafe 50%` `tactic`, one rule per lemma passed to `vericode [f, g, …]`**
  (added at the call site, so it is not part of the rule set). It is the only rule that can use a
  *specification* fact rather than build code — either by rewriting the postcondition with an
  `Eq`/`Iff`, or by applying an implication backwards and keeping what the precondition cannot
  discharge; see the section on it below.
* **`natCases` is `unsafe 20%`**: the case split. It is the only rule that has to *invent* its
  argument (the condition), so it offers one alternative per comparison of two `.nat` components
  of the input and lets the search choose. -/

/-- If `e` is a chain of product projections of `root`, return the projections outermost-first
    (`true = .1`, `false = .2`); `some []` if `e` is `root` itself; `none` otherwise. -/
partial def projPath (root e : Expr) : Option (List Bool) :=
  if e == root then some []
  else if e.isAppOfArity ``Prod.fst 3 then (projPath root e.appArg!).map (true :: ·)
  else if e.isAppOfArity ``Prod.snd 3 then (projPath root e.appArg!).map (false :: ·)
  else match e with
    | .proj ``Prod 0 inner => (projPath root inner).map (true :: ·)
    | .proj ``Prod 1 inner => (projPath root inner).map (false :: ·)
    | _ => none

/-- Close a goal `Impl s O Pre (fun inp out => out = π inp)`, where `π` is a (possibly empty)
    chain of product projections of the input, by building the whole `.fst`/`.snd`/`.var`
    implementation term in one shot and closing with `rfl`. Fails on any other goal. -/
elab "projClose" : tactic => do
  let goal ← getMainGoal
  let tgt ← instantiateMVars (← whnf (← goal.getType))
  unless tgt.isAppOf ``Impl do throwError "projClose: not an `Impl` goal"
  let #[_s, _O, _Pre, goalCond] := tgt.getAppArgs
    | throwError "projClose: malformed `Impl` goal"
  let path ← lambdaTelescope goalCond fun bs body => do
    unless bs.size == 2 do throwError "projClose: condition is not `fun inp out => …`"
    let out := bs[1]!
    let body ← whnf body
    unless body.isAppOfArity ``Eq 3 && body.getAppArgs[1]! == out do
      throwError "projClose: condition is not `out = …`"
    match projPath bs[0]! body.getAppArgs[2]! with
    | some p => pure p
    | none => throwError "projClose: RHS is not a projection of the input"
  let mut proj ← `(term| .var k)
  for p in path.reverse do
    proj ← if p then `(term| .fst $proj) else `(term| .snd $proj)
  evalTactic (← `(tactic| exact { code := .lam fun k => $proj, correct := fun _ _ => rfl }))

attribute [aesop safe apply (transparency := default) (rule_sets := [VericodeL])]
  NilTactic UnitTactic TrueTactic FalseTactic NumTactic

@[aesop safe tactic (rule_sets := [VericodeL])]
def projCloseRule : TacticM Unit := do evalTactic (← `(tactic| projClose))

attribute [aesop unsafe 90% apply (transparency := default) (rule_sets := [VericodeL])]
  ListRecTactic ListRecTactic'

attribute [aesop unsafe 70% apply (transparency := default) (rule_sets := [VericodeL])]
  ConsTactic PairTactic LETactic

@[aesop unsafe 95% tactic (rule_sets := [VericodeL])]
def pushpreRule : TacticM Unit := do evalTactic (← `(tactic| pushpre))

/-! ## Applying a helper function to a sub-list

`Reverse` (and any `out = F[sublist]` goal) is closed by *applying a helper function to a
sub-list of the input*:

* `appList` (a `RuleTac`) spots each list-valued projection `c` of the input inside the
  right-hand side and applies `AppTactic`, leaving `base := out = c` (closed by `projClose`)
  and a helper spec `step := ∀ x, f x = rhs[c ↦ x]`.
* `introTac` introduces the helper's argument, pairing it onto the input, so the helper spec
  becomes an ordinary `.list` goal `Impl (.pair I .list) .list (fun _ => True) …` — which
  `ListRecTactic` then folds. Because `AppTactic`'s helper is unconditional, this inner goal
  is precondition-free, exactly what `ListRecTactic` needs. -/

/-- Front-end for `IntroTactic` (cf. `introP`): reconstruct the residual pair-condition
    `PairPost` from a goal `Impl I (.arrow s t) Pre (fun inp f => ∀ x, body)` where `f` occurs
    only as `f x`, and apply `IntroTactic`, leaving the single paired-input subgoal. -/
elab "introTac" : tactic => do
  let goal ← getMainGoal
  let tgt ← instantiateMVars (← whnf (← goal.getType))
  unless tgt.isAppOf ``Impl do throwError "introTac: goal is not `Impl`:{indentExpr tgt}"
  let #[I, T, Pre, goalCond] := tgt.getAppArgs
    | throwError "introTac: malformed `Impl` goal"
  let Tw ← whnf T
  unless Tw.isAppOf ``Tpe.arrow do
    throwError "introTac: goal type is not an arrow:{indentExpr Tw}"
  let #[s, t] := Tw.getAppArgs
    | throwError "introTac: malformed arrow type"
  let pairPost ← lambdaTelescope goalCond fun bs body => do
    unless bs.size == 2 do throwError "introTac: condition is not `fun inp f => …`"
    let inp := bs[0]!
    let f := bs[1]!
    let body ← whnf body
    unless body.isForall do
      throwError "introTac: condition body must start with `∀ x, …`:{indentExpr body}"
    forallBoundedTelescope body (some 1) fun xs ib => do
      let x := xs[0]!
      let fx := mkApp f x
      let pairTy ← mkAppM ``Prod #[mkApp (mkConst ``Tpe.denote) I, mkApp (mkConst ``Tpe.denote) s]
      let outTy := mkApp (mkConst ``Tpe.denote) t
      withLocalDeclD `p pairTy fun p => do
      withLocalDeclD `out outTy fun out => do
        let p1 ← mkAppM ``Prod.fst #[p]
        let p2 ← mkAppM ``Prod.snd #[p]
        let ib := ib.replace fun e =>
          if e == fx then some out
          else if e == inp then some p1
          else if e == x then some p2
          else none
        if ib.containsFVar inp.fvarId! || ib.containsFVar x.fvarId! || ib.containsFVar f.fvarId! then
          throwError "introTac: `f` occurs other than as `f x`, or the argument escapes"
        mkLambdaFVars #[p, out] ib
  liftMetaTactic fun g => g.apply (mkAppN (mkConst ``IntroTactic) #[I, s, t, Pre, pairPost])

@[aesop unsafe 40% tactic (rule_sets := [VericodeL])]
def introTacRule : TacticM Unit := do evalTactic (← `(tactic| introTac))

/-- Collect every list-valued projection of `inp` occurring as a subterm of `e`. These are the
    candidate sub-lists a helper (built by `listRec`) can be applied to. -/
partial def collectListProjs (inp listNat e : Expr) : MetaM (Array Expr) := do
  let mut acc : Array Expr := #[]
  if (projPath inp e).isSome then
    if ← isDefEq (← inferType e) listNat then acc := acc.push e
  let children : Array Expr := match e with
    | .app f a         => #[f, a]
    | .lam _ d b _     => #[d, b]
    | .forallE _ d b _ => #[d, b]
    | .letE _ ty v b _ => #[ty, v, b]
    | .mdata _ b       => #[b]
    | .proj _ _ b      => #[b]
    | _                => #[]
  for c in children do
    acc := acc ++ (← collectListProjs inp listNat c)
  return acc

open Aesop in
/-- `appList`: on a goal `Impl I .list Pre (fun inp out => out = rhs)`, for each list-valued
    projection `c` of the input occurring properly inside `rhs`, apply `AppTactic` with
    `arg := fun inp => c` and `Cond := fun inp x out => out = rhs[c ↦ x]`. One backtrackable
    alternative per candidate. -/
def appList : Aesop.RuleTac := fun input => input.goal.withContext do
  let tgt ← whnf (← input.goal.getType)
  unless tgt.isAppOf ``Impl do throwError "appList: goal is not `Impl`"
  let #[I, O, Pre, goalCond] := tgt.getAppArgs | throwError "appList: malformed `Impl` goal"
  unless (← whnf O).isConstOf ``Tpe.list do throwError "appList: goal type is not `.list`"
  let listNat ← mkAppM ``List #[mkConst ``Nat]
  let es ← lambdaTelescope goalCond fun bs body => do
    unless bs.size == 2 do throwError "appList: unexpected condition shape"
    let inp := bs[0]!
    let out := bs[1]!
    let body ← whnf body
    unless body.isAppOfArity ``Eq 3 && body.getAppArgs[1]! == out do
      throwError "appList: condition is not `out = rhs`"
    let rhs := body.getAppArgs[2]!
    let raw ← collectListProjs inp listNat rhs
    let cands := raw.foldl (init := (#[] : Array Expr))
      fun acc c => if acc.any (· == c) || c == rhs then acc else acc.push c
    if cands.isEmpty then throwError "appList: no proper list-projection candidates"
    let listTpe := mkConst ``Tpe.list
    cands.mapM fun c => do
      let arg ← mkLambdaFVars #[inp] c
      withLocalDeclD `x listNat fun x => do
        let rhs' := rhs.replace fun e => if e == c then some x else none
        let cond ← mkLambdaFVars #[inp, x, out] (← mkEq out rhs')
        pure <| mkAppN (mkConst ``AppTactic) #[I, listTpe, listTpe, Pre, arg, cond]
  let initialState ← saveState
  let mut rapps : Array RuleApplication := #[]
  for e in es do
    try
      let gs ← input.goal.apply e
      let postState ← saveState
      let subgoals ← gs.toArray.mapM (mvarIdToSubgoal input.goal ·)
      rapps := rapps.push
        { goals := subgoals, postState, scriptSteps? := none, successProbability? := none }
    catch _ => pure ()
    finally restoreState initialState
  if rapps.isEmpty then throwError "appList: no candidate applied"
  return { applications := rapps }

attribute [aesop unsafe 20% (rule_sets := [VericodeL]) tactic] appList

/-! ## Lemma-driven relaxation of the postcondition

The combinators above only ever *build code*: they apply to a goal whose postcondition already
has the shape `out = <expression>`. Every step of a derivation that instead has to **use a fact
about the specification** — "this list is already sorted, so `Sorted l out` says exactly
`out = l`" — is invisible to them.

Such a step is an instance of `RelaxPostTactic`: replace `Post` by a `Post'` that implies it
*under the precondition*. `relaxPost` obtains `Post'` by **rewriting `Post` with a user-supplied
lemma**, discharging the lemma's own hypotheses from the precondition. The lemma is the only
problem-specific input, so the tactic itself stays generic. -/

/-- Decompose `proof : type` into the conjunctive *leaves* of `type`, unfolding definitions with
    `whnf` along the way (so a definition such as `Sorted l res`, which unfolds to a conjunction,
    is split too). Each leaf comes with the term proving it. This turns the single precondition
    hypothesis into a set of hypotheses that `assumption`/`simp_all` can actually use when
    discharging a rewrite's side conditions. -/
partial def preLeaves (fuel : Nat) (proof type : Expr) : MetaM (Array (Expr × Expr)) := do
  let type' ← whnf type
  if fuel != 0 && type'.isAppOfArity ``And 2 then
    let a := type'.getAppArgs[0]!
    let b := type'.getAppArgs[1]!
    -- keep the folded form too (`Sorted (p :: l) res` as well as its two conjuncts): a lemma
    -- may want either
    let here := if type == type' then #[] else #[(proof, type)]
    return here ++
      (← preLeaves (fuel - 1) (mkApp3 (mkConst ``And.left) a b proof) a) ++
      (← preLeaves (fuel - 1) (mkApp3 (mkConst ``And.right) a b proof) b)
  return #[(proof, type')]

/-- Reduce a projection of an explicit pair, `(a, b).fst ↦ a`, at the head of `e` (in both the
    `Prod.fst` and the structure-projection spelling). -/
partial def projHead (e : Expr) : Expr :=
  let compOf (p : Expr) (fst : Bool) : Expr :=
    if p.isAppOfArity ``Prod.mk 4 then projHead p.getAppArgs[if fst then 2 else 3]! else e
  if e.isAppOfArity ``Prod.fst 3 then compOf e.appArg! true
  else if e.isAppOfArity ``Prod.snd 3 then compOf e.appArg! false
  else match e with
    | .proj ``Prod 0 inner => compOf inner true
    | .proj ``Prod 1 inner => compOf inner false
    | _ => e

/-- Beta-, match- and projection-reduce `e` *everywhere*, without unfolding any definition
    (`whnfCore` only, plus `projHead`). Applying a pre/postcondition to the tuple
    `(inp.1, inp.2.1, …)` leaves a swarm of such redexes behind; they are definitionally
    irrelevant, but they make the side conditions unreadable and are a real obstacle for the
    `simp_all`/`grind` discharger. -/
def deepReduce (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun e => do
    let e' ← whnfCore (projHead e)
    return if e' == e then .done e else .visit e')

/-- The Lean type denoted by the `Tpe` expression `t`, fully unfolded (`Nat × (Nat × List Nat)`
    rather than `(Tpe.pair …).denote`). Hypotheses and goals stated in the unfolded types are what
    `simp`/`grind` can actually work with. -/
def denoteTy (t : Expr) : MetaM Expr :=
  Meta.transform (mkApp (mkConst ``Tpe.denote) t) (post := fun e => do
    if e.isAppOfArity ``Tpe.denote 1 then return .visit (← whnf e) else return .done e)

/-- `e₁` and `e₂` have the same shape up to a permutation of subterms — i.e. rewriting one into
    the other is a *permutative* step, which can always be undone. Mirrors `simp`'s private
    `isPerm`. -/
partial def isPermExpr : Expr → Expr → MetaM Bool
  | .app f₁ a₁, .app f₂ a₂ => isPermExpr f₁ f₂ <&&> isPermExpr a₁ a₂
  | .mdata _ s, t => isPermExpr s t
  | s, .mdata _ t => isPermExpr s t
  | s@(.mvar ..), t@(.mvar ..) => isDefEq s t
  | .forallE n₁ d₁ b₁ _, .forallE _ d₂ b₂ _ =>
    isPermExpr d₁ d₂ <&&> withLocalDeclD n₁ d₁ fun x => isPermExpr (b₁.instantiate1 x) (b₂.instantiate1 x)
  | .lam n₁ d₁ b₁ _, .lam _ d₂ b₂ _ =>
    isPermExpr d₁ d₂ <&&> withLocalDeclD n₁ d₁ fun x => isPermExpr (b₁.instantiate1 x) (b₂.instantiate1 x)
  | .proj _ i₁ b₁, .proj _ i₂ b₂ => pure (i₁ == i₂) <&&> isPermExpr b₁ b₂
  | s, t => return s == t

/-- Classify `lem`: is it a rewrite rule (an `Eq`/`Iff` under binders) at all, and if so, is it
    *permutative* — are its two sides equal up to a permutation of subterms, so that it can always
    be applied again to undo itself? -/
def lemmaKind (lem : Expr) : MetaM (Bool × Bool) :=
  withoutModifyingState do withNewMCtxDepth do
    let (_, _, ty) ← forallMetaTelescopeReducing (← inferType lem)
    let ty ← whnfR ty
    let sides :=
      if let some (lhs, rhs) := ty.iff? then some (lhs, rhs)
      else if let some (_, lhs, rhs) := ty.eq? then some (lhs, rhs) else none
    let some (lhs, rhs) := sides | return (false, false)
    -- A right-hand side with variables of its own (`Sorted_Cons`'s `l2`) is not permutative even
    -- if the two sides look alike: what it rewrites to depends on the side conditions, so it
    -- cannot simply be applied back. Collect the variables before `isPermExpr`, which assigns.
    let lhsVars ← getMVars lhs
    if (← getMVars rhs).any (!lhsVars.contains ·) then return (true, false)
    return (true, ← isPermExpr lhs rhs)

initialize registerTraceClass `relaxPost

private def withMaxHeartbeatsImp {α : Type} (n : Nat) (x : CoreM α) : CoreM α :=
  withReader (fun ctx => { ctx with maxHeartbeats := n }) x

/-- Run `x` with its own heartbeat budget (cf. `Core.withCurrHeartbeats`). -/
def withMaxHeartbeats {α : Type} {m : Type → Type} [Monad m] [MonadControlT CoreM m]
    (n : Nat) (x : m α) : m α :=
  controlAt CoreM fun runInBase => withMaxHeartbeatsImp n (runInBase x)

/-- Heartbeat budget for a single side-condition discharge. Discharging is a *search step*, run
    hundreds of times over a `vericode` invocation, so no single call may run away: without a
    budget, one pathological `simp_all`/`grind` goal takes the whole build down (it can recurse
    deeply enough to exhaust the stack, which no `catch` can recover from). -/
def dischargeHeartbeats : Nat := 5000 * 1000

/-- Run `tac` on `mv`; report whether it closed the goal, restoring the state if it did not. -/
def tryDischarge (mv : MVarId) (tac : TSyntax `tactic) : TacticM Bool := do
  let s ← saveState
  -- The discharger is speculative: whatever it reports — a linter warning, an error it logged
  -- instead of throwing, a heartbeat timeout — is noise from a search step the user never wrote.
  -- Keep the message log at its entry value in every outcome.
  let msgs ← Core.getMessageLog
  -- `tryCatchRuntimeEx`, not a plain `try`: an ordinary `catch` deliberately re-throws runtime
  -- exceptions, and running out of the heartbeat budget below *is* one. Here it is not an error
  -- but the answer "this side condition is not worth more time".
  tryCatchRuntimeEx
    (do
      let gs ← withMaxHeartbeats dischargeHeartbeats <| Core.withCurrHeartbeats <|
        Lean.Elab.Tactic.run mv (withoutRecover (evalTactic tac))
      Core.setMessageLog msgs
      if gs.isEmpty then return true
      trace[relaxPost] "discharger left {gs.length} goal(s) open"
      s.restore; return false)
    (fun ex => do
      if ex.isInterrupt then throw ex
      trace[relaxPost] "discharger failed: {ex.toMessageData}"
      s.restore; Core.setMessageLog msgs; return false)

/-! ### The shared context of a postcondition relaxation

Both relaxation paths (`relaxByRewrite`, `relaxByImplication`) start from the same picture of the
goal: the input as a tuple of projections, the precondition split into usable hypotheses, a fresh
output variable, and the postcondition applied to the two. `RelaxPostCtx` bundles it, and
`withRelaxPostCtx` builds it once. -/

/-- The pieces a relaxation path works with, all living in one extended local context. -/
structure RelaxPostCtx where
  /-- The `Impl` goal's input `Tpe`. -/
  I : Expr
  /-- The `Impl` goal's output `Tpe`. -/
  O : Expr
  /-- The `Impl` goal's precondition. -/
  Pre : Expr
  /-- The `Impl` goal's postcondition. -/
  Post : Expr
  /-- A fresh variable standing for the input. -/
  inp : Expr
  /-- A fresh hypothesis `Pre inp`, phrased in projections of `inp`. -/
  hpre : Expr
  /-- The conjunctive leaves of `Pre inp`: their proofs (in terms of `hpre`) and their types. -/
  leaves : Array (Expr × Expr)
  /-- One local hypothesis per entry of `leaves`, so that `assumption` can see them. -/
  leafFVars : Array Expr
  /-- A fresh variable standing for the output. -/
  out : Expr
  /-- `Post inp out`, reduced — the thing a relaxation path has to match against. -/
  target : Expr
  /-- Discharges a lemma's own hypotheses from the precondition. -/
  discharge : TSyntax `tactic

/-- Set up a `RelaxPostCtx` for the goal `Impl I O Pre Post` and run `k` in its local context.
    `ds` are the extra definitions/lemmas the side-condition discharger may use. -/
def withRelaxPostCtx (I O Pre Post : Expr) (dsArr : Array Ident)
    (k : RelaxPostCtx → TacticM Unit) : TacticM Unit := do
  let m := (decodeInputTpe I).size
  -- The discharger for the lemma's side conditions. `grind` gets the whole list; `simp_all` only
  -- gets the definitions and rewrite rules. A lemma whose conclusion is neither an equation nor a
  -- definition (say `… → Ordered (a :: l)`) is a *fact* for `grind` to instantiate, but as a simp
  -- lemma it is a conditional rewrite whose hypotheses contain variables the conclusion does not
  -- fix — simp then recurses into its own discharger and can blow the stack.
  let simpDs : Array Ident ← dsArr.filterM fun d => do
    let c ← realizeGlobalConstNoOverloadWithInfo d
    return (← getConstInfo c) matches .defnInfo _ || (← lemmaKind (← mkConstWithLevelParams c)).1
  let simpArgs : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ←
    simpDs.mapM fun d => `(Lean.Parser.Tactic.simpLemma| $d:term)
  let grindArgs : Array (TSyntax ``Lean.Parser.Tactic.grindParam) ←
    dsArr.mapM fun d => `(Lean.Parser.Tactic.grindParam| $d:ident)
  let simpAll ← if simpArgs.isEmpty then `(tactic| simp_all) else `(tactic| simp_all [$simpArgs,*])
  let grinding ← if grindArgs.isEmpty then `(tactic| grind) else `(tactic| grind [$grindArgs,*])
  let discharge ←
    `(tactic| first
        | assumption
        | ($simpAll:tactic; done)
        | ($simpAll:tactic <;> $grinding:tactic)
        | $grinding:tactic)
  withLocalDeclD `inp (← denoteTy I) fun inp => do
    -- `tuple = (inp.1, inp.2.1, …)`: definitionally `inp` (structure eta), but in constructor
    -- form, so the `match` of an anonymous-constructor lambda reduces against it.
    let mut projs := #[]
    let mut acc := inp
    for i in [0:m] do
      if i + 1 == m then
        projs := projs.push acc
      else
        projs := projs.push (← mkAppM ``Prod.fst #[acc])
        acc ← mkAppM ``Prod.snd #[acc]
    let tuple ← mkNestedTuple projs
    let preTy ← deepReduce (← whnfCore (mkApp Pre tuple))
    withLocalDeclD `hpre preTy fun hpre => do
      let leaves ← (← preLeaves 8 hpre preTy).mapM fun (prf, ty) => do
        return (prf, ← deepReduce ty)
      let decls := leaves.map fun (_, ty) => (`hle, fun (_ : Array Expr) => pure ty)
      withLocalDeclsD decls fun leafFVars => do
        withLocalDeclD `out (← denoteTy O) fun out => do
          -- `whnfCore`, not `whnf`: reduce the `match`/beta-redex of `Post` without unfolding
          -- the user's definitions, which are the very patterns `lem` matches against.
          let target ← deepReduce (← whnfCore (mkApp2 Post tuple out))
          k { I, O, Pre, Post, inp, hpre, leaves, leafFVars, out, target, discharge }

/-- Finish a relaxation: apply `RelaxPostTactic` with the new postcondition `post'`, discharge its
    side goal `∀ inp, Pre inp → ∀ out, Post' inp out → Post inp out` with `prf`, and leave the
    single `Impl I O Pre Post'` goal. -/
def finishRelaxPost (goal : MVarId) (c : RelaxPostCtx) (post' prf : Expr) : TacticM Unit := do
  let gs ← goal.apply (mkAppN (mkConst ``RelaxPostTactic) #[c.I, c.O, c.Pre, c.Post, post'])
  let mut implGoals := #[]
  for g in gs do
    if ← g.withContext do return (← whnf (← g.getType)).isAppOf ``Impl then
      implGoals := implGoals.push g
    else
      unless ← isDefEq (← g.getType) (← inferType prf) do
        throwError "relaxPost: the relaxation proof does not fit the side goal"
      g.assign prf
  replaceMainGoal implGoals.toList

/-- Run the fixpoint discharge loop on `pending`, returning the metavariables that survive it.
    Repeated, since closing one obligation may assign metavariables occurring in another. Value
    metavariables (e.g. the `l2` of `Sorted_Cons`, which the pattern does not determine) are never
    attacked directly — they are meant to be fixed by unification when a proof obligation is
    discharged. -/
def dischargeObligations (c : RelaxPostCtx) (pending : Array MVarId) : TacticM (Array MVarId) := do
  let mut pending := pending
  let mut progress := true
  while progress do
    progress := false
    let mut next := #[]
    for mv in pending do
      if ← mv.isAssigned then continue
      if ← isProp (← instantiateMVars (← mv.getType)) then
        if ← tryDischarge mv c.discharge then progress := true else next := next.push mv
      else next := next.push mv
    pending := next
  pending.filterM fun mv => return !(← mv.isAssigned)

/-! ### Path 1: relaxation by rewriting

`lem` is an `Eq`/`Iff`; rewrite `Post` with it. The new postcondition is *equivalent* to the old
one under the precondition. -/

/-- Relax the postcondition by rewriting it with the `Eq`/`Iff` lemma `lem`. -/
def relaxByRewrite (force : Bool) (goal : MVarId) (lemStx : Term) (c : RelaxPostCtx) :
    TacticM Unit := do
  -- as in `rw`: elaborate with `mayPostpone` and do *not* force synthetic metavariables —
  -- a generic lemma's implicit arguments, and hence its instances, are only determined by
  -- matching it against the postcondition
  let lem ← Term.elabTerm lemStx none true
  let ctxHolder ← mkFreshExprSyntheticOpaqueMVar (mkConst ``True)
  let r ← ctxHolder.mvarId!.rewrite c.target lem
  if (← instantiateMVars r.eNew) == c.target then
    throwError "relaxPost: the rewrite did not change the postcondition"
  -- A permutative rewrite (`Sorted (x :: y :: l) o ↔ Sorted (y :: x :: l) o`) can always
  -- be undone, so an unguarded search oscillates on it forever. Admit it in one fixed
  -- direction only, using the same term order `simp` uses for permutative rules — but
  -- in the *opposite* orientation: `simp` rewrites towards the smaller term, so the
  -- smaller term is the form a goal already has, and the only step that can expose
  -- anything new is the one towards the larger term.
  if !force && (← lemmaKind lem).2 then
    unless ← acLt c.target (← instantiateMVars r.eNew) do
      throwError "relaxPost: {lemStx} is permutative and this is its normalising \
        direction, so applying it here would loop; use `relaxPost!` to force it"
  let mut pending := #[]
  for mv in r.mvarIds do
    if ← mv.isAssigned then continue
    let ty ← instantiateMVars (← mv.getType)
    if ← isProp ty then
      pending := pending.push (← mv.replaceTargetDefEq (← deepReduce ty))
    else
      pending := pending.push mv
  let stuck ← dischargeObligations c pending
  unless stuck.isEmpty do
    let msgs := stuck.map fun mv => m!"\n{MessageData.ofGoal mv}"
    throwError "relaxPost: could not discharge the side condition(s) of \
      {lemStx}:{MessageData.joinSep msgs.toList ""}"
  let eNew ← deepReduce (← instantiateMVars r.eNew)
  let eqProof ← instantiateMVars r.eqProof
  if eNew.hasExprMVar || eqProof.hasExprMVar then
    throwError "relaxPost: the rewrite left metavariables behind:{indentExpr eNew}"
  if (c.leafFVars.push c.hpre).any (eNew.containsFVar ·.fvarId!) then
    throwError "relaxPost: the rewritten postcondition depends on the \
      precondition:{indentExpr eNew}"
  let post' ← mkLambdaFVars #[c.inp, c.out] eNew
  let prf ← withLocalDeclD `hp eNew fun hp => do
    let bridge := (← mkEqMPR eqProof hp).replaceFVars c.leafFVars (c.leaves.map (·.1))
    mkLambdaFVars #[c.inp, c.hpre, c.out, hp] bridge
  finishRelaxPost goal c post' prf

/-! ### Path 2: relaxation by implication

`lem` is not a rewrite rule but an implication `h₁ → … → hₙ → Post inp out`. Unify its
*conclusion* with the postcondition, discharge from the precondition whichever hypotheses can be,
and take the ones that survive — necessarily the ones mentioning `out` — as the new
postcondition. The result is *strictly stronger* than `Post`, which is all `RelaxPostTactic`
needs, and is the only way to make progress on a specification that does not determine its
output (see `HarderProblems.lean`: `AppendSpec` admits many outputs, so no `Iff` can turn it into
`out = …`, but `AppendSpec_cons'` can). -/

/-- Relax the postcondition by applying the implication `lem` backwards: its conclusion becomes
    the goal's postcondition, its undischarged hypotheses become the new one. -/
def relaxByImplication (goal : MVarId) (lemStx : Term) (c : RelaxPostCtx) : TacticM Unit := do
  let lem ← Term.elabTerm lemStx none true
  let (args, _, concl) ← forallMetaTelescopeReducing (← inferType lem)
  unless ← isDefEq (← deepReduce concl) c.target do
    throwError "relaxPost: the conclusion of {lemStx} does not match the \
      postcondition:{indentExpr c.target}"
  let full := mkAppN lem args
  let mut pending := #[]
  for a in args do
    let mv := a.mvarId!
    if ← mv.isAssigned then continue
    let ty ← instantiateMVars (← mv.getType)
    if ← isProp ty then pending := pending.push (← mv.replaceTargetDefEq (← deepReduce ty))
    else pending := pending.push mv
  let stuck ← dischargeObligations c pending
  -- Everything the precondition could not settle becomes the new postcondition, so no proof
  -- obligation is dropped — but a *value* the lemma leaves open is not an obligation, it is an
  -- under-determined instance, and turning it into a postcondition would smuggle a metavariable
  -- into the specification.
  let mut hypTys := #[]
  for mv in stuck do
    let ty ← instantiateMVars (← mv.getType)
    unless ← isProp ty do
      throwError "relaxPost: {lemStx} leaves the value argument \
        undetermined:{indentExpr (← mv.getType)}"
    let ty ← deepReduce ty
    if (c.leafFVars.push c.hpre).any (ty.containsFVar ·.fvarId!) then
      throwError "relaxPost: a residual obligation of {lemStx} depends on the \
        precondition:{indentExpr ty}"
    hypTys := hypTys.push ty
  if hypTys.isEmpty then
    throwError "relaxPost: {lemStx} proves the postcondition for every output, so it leaves \
      nothing to implement; close the goal with `UseTactic` instead"
  let post'Body := mkAndN hypTys.toList
  if post'Body.hasExprMVar then
    throwError "relaxPost: the residual obligation has metavariables:{indentExpr post'Body}"
  let post' ← mkLambdaFVars #[c.inp, c.out] post'Body
  let prf ← withLocalDeclD `hp post'Body fun hp => do
    let mut comps := #[]
    let mut cur := hp
    for i in [0:hypTys.size] do
      if i + 1 == hypTys.size then comps := comps.push cur
      else
        comps := comps.push (← mkAppM ``And.left #[cur])
        cur ← mkAppM ``And.right #[cur]
    -- the surviving obligations are still metavariables inside `full`; replace each by the
    -- matching component of `hp` (cf. the `replaceFVars` for the precondition leaves)
    let body := (← instantiateMVars full).replace fun e => match e with
      | .mvar id => (stuck.findIdx? (· == id)).map (comps[·]!)
      | _ => none
    let body := body.replaceFVars c.leafFVars (c.leaves.map (·.1))
    mkLambdaFVars #[c.inp, c.hpre, c.out, hp] body
  finishRelaxPost goal c post' prf

/-- `relaxPost lem [d₁, …, dₖ]` weakens the postcondition of a goal `Impl I O Pre Post` to a
`Post'` that implies it *under the precondition*, leaving the single goal `Impl I O Pre Post'`.
Any hypothesis of `lem` becomes a side condition, proved *from the precondition* by `assumption`,
`simp_all [d₁, …, dₖ]` and `grind [d₁, …, dₖ]`. No proof obligation is ever silently dropped.

There are two ways `lem` can produce `Post'`, tried in this order:

* **by rewriting.** `lem` is an `Eq`/`Iff`: rewrite `Post` with it. `Post'` is then *equivalent*
  to `Post`. This is how `SortedOrdered_iff : Ordered l1 → (Sorted l1 l2 ↔ l2 = l1)` turns a
  specification into the `out = …` shape the code-building combinators need.
* **by implication.** `lem` is `h₁ → … → hₙ → Post inp out`: unify its conclusion with `Post`,
  discharge from the precondition whichever `hᵢ` can be, and take the survivors (conjoined) as
  `Post'`, which is then *strictly stronger* than `Post`. This is the only path available when
  the specification does not determine its output — `AppendSpec` in `HarderProblems.lean` admits
  many correct outputs, so no `Iff` can rewrite it to `out = …`, but
  `AppendSpec_cons' : AppendSpec (a, l1) l2 → l3 = b :: l2 → AppendSpec (a, b :: l1) l3` relaxes
  `AppendSpec (a, b :: l1) out` to `out = b :: res` in one step, with `l2 := res` recovered from
  the precondition by `assumption`.

The precondition is made available to that discharger both as-is and split into its conjunctive
leaves (see `preLeaves`), which is what lets `assumption` instantiate the metavariables a
rewrite leaves behind: rewriting `Sorted (a :: p :: l) out` with
`Sorted_Cons : l1.Perm l2 → (Sorted (x :: l1) l3 ↔ Sorted (x :: l2) l3)` yields
`Sorted (a :: ?l2) out` plus the side condition `(p :: l).Perm ?l2`, and `assumption` picks
`?l2 := res` out of the precondition.

A *permutative* lemma (one whose two sides differ only by a permutation of subterms, such as
`Sorted_Swap`) can always be applied again to undo itself, so a search that uses it never
terminates. `relaxPost` therefore admits such a lemma in one direction only, fixed by the same
term order `simp` uses for permutative rules — but in the opposite orientation: `simp` rewrites
towards the smaller term, so the smaller term is the shape a goal already has, and the step that
can expose something new is the one towards the larger term. `relaxPost! lem` skips the check,
for steering a derivation by hand in the direction the order forbids. -/
syntax (name := relaxPostStx) "relaxPost" ppSpace term:max (" [" ident,* "]")? : tactic
syntax (name := relaxPostForceStx) "relaxPost!" ppSpace term:max (" [" ident,* "]")? : tactic

/-- The implementation of `relaxPost`; `force` disables the permutative-direction check. -/
def relaxPostCore (force : Bool) (lemStx : Term)
    (ds : Option (Syntax.TSepArray `ident ",")) : TacticM Unit := withMainContext do
  let dsArr : Array Ident := match ds with | some ds => ds.getElems | none => #[]
  let goal ← getMainGoal
  let tgt ← instantiateMVars (← whnf (← goal.getType))
  unless tgt.isAppOf ``Impl do
    throwError "relaxPost: goal is not `Impl I O Pre Post`:{indentExpr tgt}"
  let #[I, O, Pre, Post] := tgt.getAppArgs
    | throwError "relaxPost: malformed `Impl` goal:{indentExpr tgt}"
  withRelaxPostCtx I O Pre Post dsArr fun c => do
    -- A plain `try`, not `tryCatchRuntimeEx`: an ordinary `catch` re-throws runtime exceptions,
    -- and a path that ran out of heartbeats should abort rather than send us into a second,
    -- equally expensive attempt. Only "this lemma does not fit" is worth falling back on.
    let s ← saveState
    try
      relaxByRewrite force goal lemStx c
    catch rwEx =>
      let rwMsg ← rwEx.toMessageData.toString
      s.restore
      try
        relaxByImplication goal lemStx c
      catch impEx =>
        let impMsg ← impEx.toMessageData.toString
        s.restore
        throwError "relaxPost: {lemStx} does not apply here.\n\
          As a rewrite: {rwMsg}\n\
          As an implication: {impMsg}"

elab_rules : tactic
  | `(tactic| relaxPost! $lemStx $[[$ds,*]]?) => relaxPostCore true lemStx ds
  | `(tactic| relaxPost $lemStx $[[$ds,*]]?)  => relaxPostCore false lemStx ds

/-! ## Inventing the case split

Branching is the one construction the search cannot read off the postcondition: `CasesTactic`
takes the condition `cond` as an argument, and nothing in the goal says what it should be. But in
this language a condition can only ever be a comparison of two numbers (`Trm'.le` and `Trm'.ite`
are the only decision primitives), so at a goal whose input carries **two `.nat` components** —
which is exactly the situation after `ListRecTactic` on an insertion-style problem, where the
element being inserted and the head of the list are both in scope — there are only finitely many
conditions to try. `natCases` offers each of them as a backtrackable alternative. -/

/-- The operand pairs of every `≤`/`<` comparison occurring in `e`. -/
partial def collectComparisons (e : Expr) : Array (Expr × Expr) :=
  let here : Option (Expr × Expr) :=
    let args := e.getAppArgs
    if e.isAppOfArity ``Nat.ble 2 || e.isAppOfArity ``Nat.blt 2 ||
       e.isAppOfArity ``Nat.le 2 || e.isAppOfArity ``Nat.lt 2 then
      some (args[0]!, args[1]!)
    else if e.isAppOfArity ``LE.le 4 || e.isAppOfArity ``LT.lt 4 then
      some (args[2]!, args[3]!)
    else none
  let children : Array Expr := match e with
    | .app f a         => #[f, a]
    | .lam _ d b _     => #[d, b]
    | .forallE _ d b _ => #[d, b]
    | .letE _ t v b _  => #[t, v, b]
    | .mdata _ b       => #[b]
    | .proj _ _ b      => #[b]
    | _                => #[]
  let acc := children.foldl (init := (#[] : Array (Expr × Expr)))
    fun acc c => acc ++ collectComparisons c
  match here with
  -- a comparison under a binder (`∀ x ∈ l, a ≤ x`) is about the bound variable, not about the
  -- input; its operands are loose bound variables, which must never reach `isDefEq`
  | some (a, b) => if a.hasLooseBVars || b.hasLooseBVars then acc else acc.push (a, b)
  | none   => acc

/-- Does `e` compare `x` and `y`, in either order? Used to tell whether the precondition already
    fixes the order of two numbers. The operands are compared up to definitional equality: the
    same projection of the input may appear with `ℕ` in one place and the unreduced
    `Tpe.nat.denote` in the other. -/
def comparesPair (e x y : Expr) : MetaM Bool :=
  (collectComparisons e).anyM fun (a, b) => withoutModifyingState do
    return (← isDefEq a x) && (← isDefEq b y) || (← isDefEq a y) && (← isDefEq b x)

open Aesop in
/-- `natCases`: on a goal `Impl I O Pre Post` whose input has at least two `.nat` components,
    apply `CasesTactic` with `cond := fun inp => Nat.ble πᵢ πⱼ` for each ordered pair of distinct
    nat projections. One backtrackable alternative per candidate, each with a *concrete* `cond` —
    an `apply CasesTactic` with `cond` left as a metavariable would be shared across the three
    subgoals and reconstructed by aesop as `sorry` (cf. `projClose`).

    A pair whose order the precondition already fixes is skipped: splitting on it would produce
    one vacuous branch and, since both branches keep the input type, the search would otherwise
    split on the same two numbers forever. -/
def natCases : Aesop.RuleTac := fun input => input.goal.withContext do
  let tgt ← whnf (← input.goal.getType)
  unless tgt.isAppOf ``Impl do throwError "natCases: goal is not `Impl`"
  let #[I, O, Pre, Post] := tgt.getAppArgs | throwError "natCases: malformed `Impl` goal"
  let comps := decodeInputTpe I
  let m := comps.size
  let es ← withLocalDeclD `inp (← denoteTy I) fun inp => do
    let mut projs := #[]
    let mut acc := inp
    for i in [0:m] do
      if i + 1 == m then
        projs := projs.push acc
      else
        projs := projs.push (← mkAppM ``Prod.fst #[acc])
        acc ← mkAppM ``Prod.snd #[acc]
    let nats := (Array.range m).filterMap fun i =>
      if comps[i]!.isConstOf ``Tpe.nat then some projs[i]! else none
    if nats.size < 2 then throwError "natCases: fewer than two `.nat` components"
    let tuple ← mkNestedTuple projs
    -- Nothing to decide once the postcondition names the output outright: the constructive
    -- combinators build `out = rhs` directly. Skipping those goals is also what stops the rule
    -- from splitting the boolean condition goal it just created — that goal's postcondition is
    -- `out = Nat.ble …`, and splitting it reproduces itself forever.
    withLocalDeclD `out (← denoteTy O) fun out => do
      let body ← deepReduce (← whnfCore (mkApp2 Post tuple out))
      if body.isAppOfArity ``Eq 3 && body.getAppArgs[1]! == out then
        throwError "natCases: the postcondition already determines the output"
    -- the precondition, phrased in the same projections (see `relaxPostCore` for the tuple trick)
    let preTy ← deepReduce (← whnfCore (mkApp Pre tuple))
    let mut cands := #[]
    for i in [0:nats.size] do
      for j in [0:nats.size] do
        if i != j && !(← comparesPair preTy nats[i]! nats[j]!) then
          let cond ← mkLambdaFVars #[inp] (← mkAppM ``Nat.ble #[nats[i]!, nats[j]!])
          cands := cands.push (mkAppN (mkConst ``CasesTactic) #[I, O, Pre, Post, cond])
    if cands.isEmpty then throwError "natCases: the precondition already orders every pair"
    pure cands
  let initialState ← saveState
  let mut rapps : Array RuleApplication := #[]
  for e in es do
    try
      let gs ← input.goal.apply e
      let postState ← saveState
      let subgoals ← gs.toArray.mapM (mvarIdToSubgoal input.goal ·)
      rapps := rapps.push
        { goals := subgoals, postState, scriptSteps? := none, successProbability? := none }
    catch _ => pure ()
    finally restoreState initialState
  if rapps.isEmpty then throwError "natCases: no candidate applied"
  return { applications := rapps }

attribute [aesop unsafe 20% (rule_sets := [VericodeL]) tactic] natCases

/-- Search for a vericoding derivation by backtracking over the `VericodeL` rule set.

`vericode [f, g, …]` hands `f`, `g`, … to aesop in two ways:
* as **norm-simp** lemmas (as in `simp [f, g]`), to expose problem-specific definitions the
  combinators would not otherwise see through, and
* as one `relaxPost` **search step each**: at every `Impl` goal aesop may relax the
  postcondition with that lemma — by rewriting with it if it is an `Eq`/`Iff`, otherwise by
  applying it as an implication — discharging the lemma's own hypotheses from the precondition
  (the whole list is available to the discharger's `simp_all`/`grind`). One rule per lemma, so
  the search backtracks over them like over any other combinator.

The second form is what conditional lemmas need: a lemma such as
`Ordered l1 → (Sorted l1 l2 ↔ l2 = l1)` can never fire as a simp lemma inside `Post`, because
the precondition is a *different argument* of `Impl` and not in scope there.

Each lemma is routed by shape:
* a **definition** to unfold: norm-simp only — `relaxPost` has nothing to match it against;
* a **permutative** rewrite rule (`Sorted_Swap`): `relaxPost` only. As a simp lemma it would
  normalise the postcondition back after every step of the search, undoing exactly the step that
  exposes the next rewrite;
* anything else (a plain rewrite rule, or an implication such as `AppendSpec_cons'` whose
  conclusion is not `Eq`/`Iff`): both. `relaxPost` decides at run time which of its two paths
  applies. -/
syntax "vericode" (" [" ident,* "]")? : tactic

elab_rules : tactic
  | `(tactic| vericode) => do evalTactic (← `(tactic| aesop (rule_sets := [VericodeL])))
  | `(tactic| vericode [$ls,*]) => do
    let mut rules : Array (TSyntax `Aesop.rule_expr) := #[]
    for l in ls.getElems do
      let c ← realizeGlobalConstNoOverloadWithInfo l
      let isDefn := (← getConstInfo c) matches .defnInfo _
      let (isRw, isPerm) ← lemmaKind (← mkConstWithLevelParams c)
      if !isDefn then
        rules := rules.push (← `(Aesop.rule_expr| unsafe 50% tactic (by relaxPost $l:ident [$ls,*])))
      if isDefn || (isRw && !isPerm) then
        rules := rules.push (← `(Aesop.rule_expr| norm simp $l:ident))
    evalTactic (← `(tactic| aesop (rule_sets := [VericodeL]) (add $rules,*)))
