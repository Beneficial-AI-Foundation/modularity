import DeductiveVericoding.ListLanguage.Problems

open ListLanguage

/-!
# Solutions

Implementations for the specifications in `Problems.lean`. Each `XXXSolution` is a hand-written
term together with its correctness proof.
-/

def UnitSolution : UnitProblem := {
  code := .lam fun _ => .unit
  correct _ _ := rfl
}

def NilSolution : NilProblem := {
  code := .lam fun _ => .nil
  correct _ _ := rfl
}

def ConsSolution : ConsProblem := {
  code := .lam fun k => .cons (.fst (.var k)) (.snd (.var k))
  correct _ _ := rfl
}

def NumToListSolution : NumToListProblem := {
  code := .lam fun k => .cons (.var k) .nil
  correct _ _ := rfl
}

def List123Solution : List123Problem := {
  code := .lam fun _ => .cons (.num 1) (.cons (.num 2) (.cons (.num 3) .nil))
  correct _ _ := rfl
}

def AppendConstantSolution : AppendConstantProblem := {
  code := .lam fun l => .app
    (.listRec (.lam fun _ => .cons (.num 1) .nil)
      (.lam fun p => .cons (.fst (.snd (.var p))) (.snd (.snd (.snd (.var p))))))
    (.mkPair .unit (.var l))
  correct inp _ := by
    induction inp with
    | nil => rfl
    | cons a l ih =>
      simp [Trm.eval, Trm'.eval, Trm'.eval.go] at ⊢ ih
      congr
}

def AppendSolution : AppendProblem := {
  code := .listRec (.lam fun k => .cons (.var k) .nil) (.lam fun p => .cons (.fst (.snd (.var p))) (.snd (.snd (.snd (.var p)))))
  correct inp _ := by
    obtain ⟨a, l⟩ := inp
    induction l with
    | nil => rfl
    | cons a l ih =>
      simp [Trm.eval, Trm'.eval, Trm'.eval.go] at ⊢ ih
      congr
}

-- def ReverseSolution : ReverseProblem := {
--   code := .lam fun l => .app (.listRec (.lam fun _ => .nil) AppendSolution.code)
--     (.mkPair .unit (.var l))
--   correct inp _ := by
--     induction inp with
--     | nil => rfl
--     | cons a l ih =>
--       simp [Trm.eval, Trm'.eval, Trm'.eval.go] at ih ⊢
--       rw [ih]
--       exact AppendSolution.correct (a, l.reverse) trivial
-- }

def ConcatSolution : ConcatProblem := {
  code := .listRec (.lam fun k => (.var k)) (.lam fun p => .cons (.fst (.snd (.var p))) (.snd (.snd (.snd (.var p)))))
  correct inp _ := by
    obtain ⟨l1, l2⟩ := inp
    induction l2 with
    | nil => rfl
    | cons a l ih =>
      simp [Trm.eval, Trm'.eval, Trm'.eval.go] at ih ⊢
      rw [ih]
}
