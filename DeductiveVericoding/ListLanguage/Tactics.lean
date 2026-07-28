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
