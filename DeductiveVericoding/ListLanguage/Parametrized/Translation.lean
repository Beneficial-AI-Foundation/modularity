import DeductiveVericoding.ListLanguage.Parametrized.Basic

open ListLanguage

namespace Parametrized

/-! ## Translation to `ListLanguage` (de Bruijn → PHOAS) -/

/-- Translate a parameter access to the old PHOAS language under a `rep`-environment:
    an in-scope parameter becomes `.var` of its bound value; an out-of-scope one is `.unit`. -/

instance instInhabitedTrm' {rep : Tpe → Type} : (t : Tpe) → Inhabited (Trm' rep t)
  | .unit => ⟨.unit⟩
  | .bool => ⟨.false⟩
  | .nat => ⟨.num 0⟩
  | .list => ⟨.nil⟩
  | .pair t u => ⟨.mkPair (instInhabitedTrm' t).default (instInhabitedTrm' u).default⟩
  | .arrow _ u => ⟨.lam fun _ => (instInhabitedTrm' u).default⟩

def parTrans {rep : Tpe → Type} : {Γ : Ctx} → Env rep Γ → (i : Nat) → (t : Tpe) →
    ListLanguage.Trm' rep t
  | [], _, _, _ => default
  | s :: _, (x, _), 0, t => if h : s = t then h ▸ .var x else default
  | _ :: _, (_, ρ), i + 1, t => parTrans ρ i t

/-- Translate a de Bruijn term to a PHOAS term of the old language: each `.lam` becomes a
    PHOAS `.lam` binding a fresh variable, pushed onto the translation environment `ρ`. -/
def toList' {rep : Tpe → Type} : {Γ : Ctx} → {t : Tpe} → Trm Γ t → Env rep Γ →
    ListLanguage.Trm' rep t
  | _, _, .unit, _ => .unit
  | _, _, .nil, _ => .nil
  | _, _, .num n, _ => .num n
  | _, _, .par i s, ρ => parTrans ρ i s
  | _, _, .cons h t, ρ => .cons (toList' h ρ) (toList' t ρ)
  | _, _, .mkPair a b, ρ => .mkPair (toList' a ρ) (toList' b ρ)
  | _, _, .fst e, ρ => .fst (toList' e ρ)
  | _, _, .snd e, ρ => .snd (toList' e ρ)
  | _, _, .lam body, ρ => .lam (fun x => toList' body (x, ρ))
  | _, _, .app f a, ρ => .app (toList' f ρ) (toList' a ρ)
  | _, _, .listRec base step, ρ => ListLanguage.Trm'.listRec
    (.lam fun _ => toList' base ρ)
    (.lam fun a => .lam fun l => .lam fun res => toList' step (a, (l, (res, ρ))))
  | _, _, .true, _ => .true
  | _, _, .false, _ => .false
  | _, _, .le e1 e2, env => .le (toList' e1 env) (toList' e2 env)
  | _, _, .ite c t e, env => .ite (toList' c env) (toList' t env) (toList' e env)

/-- A closed de Bruijn term translates to a closed old-language term. -/
def toClosed {t : Tpe} (e : Trm [] t) : ListLanguage.Trm t := fun {_rep} => toList' e ()

/-- The translation preserves the parameter-lookup value. -/
theorem parTrans_eval : {Γ : Ctx} → (ρ : Env Tpe.denote Γ) → (i : Nat) → (t : Tpe) →
    (parTrans ρ i t).eval = Env.getT ρ i t
  | [], _, _, t => sorry
  | s :: _, (_, _), 0, t => by
    by_cases h : s = t
    · simp [parTrans, Env.getT, dif_pos h, Trm'.eval, Env.get]
      sorry
    sorry
  | _ :: _, (_, ρ), i + 1, t => parTrans_eval ρ i t

/-- The old-language `listRec` (curried step `head → tail → rec`) evaluates as `listFold`. -/
theorem old_listRec_eval
    (ob : ListLanguage.Trm' Tpe.denote (.arrow .unit .list))
    (os : ListLanguage.Trm' Tpe.denote (.arrow .nat (.arrow .list (.arrow .list .list)))) :
    ∀ xs, (ListLanguage.Trm'.listRec ob os).eval xs
        = listFold (ob.eval ()) (fun a l res => os.eval a l res) xs
  | [] => rfl
  | a :: l => by
      show os.eval a l ((ListLanguage.Trm'.listRec ob os).eval l)
         = os.eval a l (listFold (ob.eval ()) (fun a l res => os.eval a l res) l)
      rw [old_listRec_eval ob os l]

/-- **Semantic agreement**: the translated old-language term evaluates identically to the
    de Bruijn term. This is what lets correctness transfer across the translation. -/
theorem toList'_eval : ∀ {Γ : Ctx} {t : Tpe} (e : Trm Γ t) (ρ : Env Tpe.denote Γ),
    (toList' e ρ).eval = e.eval ρ := by
  intro Γ t e
  induction e with
  | unit => intro ρ; rfl
  | nil => intro ρ; rfl
  | num n => intro ρ; rfl
  | par i s => intro ρ; exact parTrans_eval ρ i s
  | cons h t ih_h ih_t => intro ρ; simp only [toList', Trm.eval, Trm'.eval, ih_h, ih_t]
  | mkPair a b ih_a ih_b => intro ρ; simp only [toList', Trm.eval, Trm'.eval, ih_a, ih_b]
  | fst e ih => intro ρ; simp only [toList', Trm.eval, Trm'.eval, ih]
  | snd e ih => intro ρ; simp only [toList', Trm.eval, Trm'.eval, ih]
  | lam body ih => intro ρ; funext v; simp only [toList', Trm.eval, Trm'.eval]; exact ih (v, ρ)
  | app f a ih_f ih_a => intro ρ; simp only [toList', Trm.eval, Trm'.eval, ih_f, ih_a]
  | listRec base step ih_base ih_step =>
      intro ρ
      funext L
      induction L with
      | nil => simp [Trm.eval, Trm'.eval, toList', ih_base, Trm'.eval.go, listFold]
      | cons a l ih =>
        simp [Trm.eval, Trm'.eval, toList', ih_base, ih_step, Trm'.eval.go, listFold] at ⊢ ih
        rw [ih]
  | false => intro env; rfl
  | true => intro env; rfl
  | le e1 e2 ih1 ih2 => intro env; simp only [toList', Trm.eval, Trm'.eval, ih1, ih2]
  | ite c t e ihc iht ihe => intro env; simp only [toList', Trm.eval, Trm'.eval, ihe, iht, ihc]


/-- **Translate a Problem**: a solved parametrized implementation of `inTpe ⟶ outTpe` (with
    the input introduced as the single parameter) becomes a genuine `ListLanguage.Impl`.
    Correctness transfers via `toList'_eval`. -/
def toImpl (inTpe outTpe : Tpe) (Pre : inTpe.denote → Prop)
    (Post : inTpe.denote → outTpe.denote → Prop)
    (impl : ImplP [] (.arrow inTpe outTpe) (fun _ f => ∀ inp, Pre inp → Post inp (f inp))) :
    ListLanguage.Impl inTpe outTpe Pre Post :=
  { code := toClosed impl.code
    correct := fun inp hpre => by
      have h := impl.correct () inp hpre
      simp only [ListLanguage.Trm.eval, toClosed]
      rw [toList'_eval impl.code ()]
      exact h }

-- def SolveImpl (inTpe outTpe : Tpe) (Pre : inTpe.denote → Prop)
--     (Post : inTpe.denote → outTpe.denote → Prop)
--     (body : ImplP [inTpe] outTpe (fun env out => Pre (env.getT 0 inTpe) → Post (env.getT 0 inTpe) out)) :
--     ListLanguage.Impl inTpe outTpe Pre Post :=
--   toImpl inTpe outTpe Pre Post (IntroP [] inTpe outTpe _ body)

end Parametrized
