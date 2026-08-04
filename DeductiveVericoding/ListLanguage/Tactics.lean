import DeductiveVericoding.ListLanguage.Basic

/- # TACTICS : Here we have a collection of vericoding tactics-/

open ListLanguage

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
