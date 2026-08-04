import DeductiveVericoding.ListLanguage.Basic
import Lean

/- # TACTICS : Here we have a collection of vericoding tactics-/

open ListLanguage
open Lean Elab Tactic Meta

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

--maybe this is not needed
def SplitTactic (s t u : Tpe) {Pre : s.denote → Prop} (target : s.denote → t.denote) (Post : t.denote → u.denote → Prop)
  (base : Impl s t Pre (fun inp out => out = target inp))
  (step : Impl t u (fun _ => True) Post) :
    Impl s u Pre (fun inp out => Post (target inp) out) :=
  { code := .lam fun k => .app step.code (.app base.code (.var k))
    correct inp pre := by
      have : base.code.eval inp = target inp := base.correct inp pre
      simp [Trm.eval, Trm'.eval, this]
      exact step.correct (target inp) (by trivial)
  }

def ListRecTactic {t : Tpe} {Post : t.denote × List Nat → List Nat → Prop}
  (base : Impl t .list (fun _ ↦ True) (fun p out ↦ Post (p, []) out))
  (step : Impl (.pair t (.pair .nat (.pair .list .list))) .list (fun (p, (_, (l, res))) ↦ Post (p, l) res) (fun (p, (a, (l, _))) out ↦ Post (p, (a :: l)) out)) :
    Impl (.pair t .list) .list (fun _ ↦ True) Post :=
  { code := .listRec base.code step.code
    correct inp _ := by
      obtain ⟨par, l⟩ := inp
      induction l with
      | nil => exact base.correct par (by trivial)
      | cons a l ih => exact step.correct ⟨par, ⟨a, ⟨l, _⟩⟩⟩ ih
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
    applying a helper function `step : I → (s → t)` to the argument `arg inp`. This is the
    non-parametrized analogue of the parametrized `AppPTactic`: the helper is unconditional
    (`fun _ => True`), so the recursion that builds it (via `IntroTactic`/`ListRecTactic`) is
    free of the ambient precondition. -/
def AppTactic (I s t : Tpe) (Pre : I.denote → Prop) (arg : I.denote → s.denote)
    (Cond : I.denote → s.denote → t.denote → Prop)
    (base : Impl I s Pre (fun inp out => out = arg inp))
    (step : Impl I (.arrow s t) (fun _ => True) (fun inp f => ∀ x, Cond inp x (f x))) :
    Impl I t Pre (fun inp out => Cond inp (arg inp) out) :=
  { code := .lam fun k => .app (.app step.code (.var k)) (.app base.code (.var k))
    correct inp pre := by
      have hb : base.code.eval inp = arg inp := base.correct inp pre
      show Cond inp (arg inp) (step.code.eval inp (base.code.eval inp))
      rw [hb]
      exact step.correct inp trivial (arg inp)
  }

/-- **Introduce the argument of a helper.** Turn a solved `Impl (.pair I s) t` (with the new
    argument paired onto the input) into an arrow-valued `Impl I (.arrow s t)`. The dual of
    `AppTactic`; the non-parametrized analogue of the parametrized `IntroPTactic`. -/
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
    weakened. This is the non-parametrized analogue of `RelaxCondPTactic`. -/
def RelaxTactic (I O : Tpe) (Pre : I.denote → Prop) (Post Post' : I.denote → O.denote → Prop)
    (impl : Impl I O Pre Post')
    (h : ∀ inp, Pre inp → ∀ out, Post' inp out → Post inp out) :
    Impl I O Pre Post :=
  { code := impl.code
    correct := fun inp hpre => h inp hpre _ (impl.correct inp hpre) }

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
relaxes to `Post' := fun inp out => (… s …)[s ↦ x]`, and applies `RelaxTactic`, discharging
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
  let e := mkAppN (mkConst ``RelaxTactic) #[I, O, Pre, Post, post']
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
