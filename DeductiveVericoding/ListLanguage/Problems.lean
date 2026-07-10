import DeductiveVericoding.ListLanguage.Basic

open ListLanguage

/-
Here we have a collection of vericoding Problems in the List language defined in ListLanguage.lean
-/

abbrev UnitProblem := Impl .unit .unit (fun _ => True) (fun _ out => out = ())

def UnitSolution : UnitProblem := {
  code := .lam fun _ => .unit
  correct _ _ := rfl
}

abbrev NilProblem := Impl .unit .list (fun _ => True) (fun _ out => out = [])

def NilSolution : NilProblem := {
  code := .lam fun _ => .nil
  correct _ _ := rfl
}

abbrev ConsProblem := Impl (.pair .nat .list) .list (fun _ => True) (fun ⟨x, xs⟩ out => out = x :: xs)

def ConsSolution : ConsProblem := {
  code := .lam fun k => .cons (.fst (.var k)) (.snd (.var k))
  correct _ _ := rfl
}

abbrev NumToListProblem := Impl .nat .list (fun _ => True) (fun x out => out = [x])

def NumToListSolution : NumToListProblem := {
  code := .lam fun k => .cons (.var k) .nil
  correct _ _ := rfl
}

abbrev List123Problem := Impl .unit .list (fun _ => True) (fun _ out => out = [1,2,3])

def List123Solution : List123Problem := {
  code := .lam fun _ => .cons (.num 1) (.cons (.num 2) (.cons (.num 3) .nil))
  correct _ _ := rfl
}

abbrev AppendConstantProblem := Impl .list .list (fun _ => True) (fun inp out => out = inp.append [1])

def AppendConstantSolution : AppendConstantProblem := {
  code := .listRec (.lam fun _ => .cons (.num 1) .nil) (.lam fun a => .lam fun _  => .lam fun res => .cons (.var a) (.var res))
  correct inp _ := by
    induction inp with
    | nil => rfl
    | cons a l ih =>
      simp [Trm.eval, Trm'.eval, Trm'.eval.go] at ⊢ ih
      congr
}

abbrev AppendProblem := Impl (.pair .nat .list) .list (fun _ => True) (fun ⟨a, l⟩ out => out = l.append [a])

def AppendSolution : AppendProblem := {
  code := .lam fun k => .app (.listRec (.lam fun _ => .cons (.fst (.var k)) .nil) (.lam fun a => .lam fun _  => .lam fun res => .cons (.var a) (.var res))) (.snd (.var k))
  correct inp _ := by
    obtain ⟨a, l⟩ := inp
    induction l with
    | nil => rfl
    | cons a l ih =>
      simp [Trm.eval, Trm'.eval, Trm'.eval.go] at ⊢ ih
      congr
}

abbrev ReverseProblem := Impl .list .list (fun _ => True) (fun l out => out = l.reverse)

def ReverseSolution : ReverseProblem := {
  code := .listRec (.lam fun _ => .nil) (.lam fun a => .lam fun _  => .lam fun res => .app AppendSolution.code (.mkPair (.var a) (.var res)))
  correct inp _ := by
    induction inp with
    | nil => rfl
    | cons a l ih =>
      simp [Trm.eval, Trm'.eval, Trm'.eval.go] at ih ⊢
      rw [ih]
      exact AppendSolution.correct (a, l.reverse) trivial
}

abbrev ConcatProblem := Impl (.pair .list .list) .list (fun _ => True) (fun ⟨l1, l2⟩ out => out = l1.append l2)

def ConcatSolution : ConcatProblem := {
  code := .lam fun k => .app (.listRec (.lam fun _ => .snd (.var k))  (.lam fun a => .lam fun _  => .lam fun res => .cons (.var a) (.var res))) (.fst (.var k))
  correct inp _ := by
    obtain ⟨l1, l2⟩ := inp
    induction l1 with
    | nil => rfl
    | cons a l ih =>
      simp [Trm.eval, Trm'.eval, Trm'.eval.go] at ih ⊢
      rw [ih]
}
