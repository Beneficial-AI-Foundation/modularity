import DeductiveVericoding.ListLanguage.Problems
import DeductiveVericoding.ListLanguage.Tactics

open ListLanguage

/-!
# Solutions

Implementations for the specifications in `Problems.lean`. Each `XXXSolution` is a hand-written
term together with its correctness proof; each `XXXSolution'` is the same problem derived by
`apply`ing the combinators from `Tactics.lean` instead.
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

/-! # Derivations via the vericoding combinators

The same problems, solved by `apply`ing the combinators of `Tactics.lean` rather than writing
the term out. The `listRec` step goals follow the `simp; pushpre` idiom. `ReverseSolution'`
needs one extra move: `SplitTactic` permutes the packed input so the append helper sees its
arguments in the order it expects. -/

def UnitSolution' : UnitProblem := by
  apply UnitTactic

#eval ListLanguage.Trm.pretty UnitSolution'.code

def NilSolution' : NilProblem := by
  apply NilTactic

#eval ListLanguage.Trm.pretty NilSolution'.code

def ConsSolution' : ConsProblem := by
  apply ConsTactic
  · apply FstTactic
    apply IdentityTactic
  apply SndTactic
  apply IdentityTactic

#eval ListLanguage.Trm.pretty ConsSolution'.code

def NumToListSolution' : NumToListProblem := by
  apply ConsTactic
  · apply IdentityTactic
  apply NilTactic

#eval ListLanguage.Trm.pretty NumToListSolution'.code

def List123Solution' : List123Problem := by
  apply ConsTactic
  · apply NumTactic
  apply ConsTactic
  · apply NumTactic
  apply ConsTactic
  · apply NumTactic
  apply NilTactic

#eval ListLanguage.Trm.pretty List123Solution'.code

def AppendConstantSolution' : AppendConstantProblem := by
  apply ListRecTactic'
  · simp
    apply ConsTactic
    · apply NumTactic
    apply NilTactic
  simp
  pushpre
  apply ConsTactic
  · apply FstTactic
    apply IdentityTactic
  apply SndTactic
  apply SndTactic
  apply IdentityTactic

#eval ListLanguage.Trm.pretty AppendConstantSolution'.code

def AppendSolution' : AppendProblem := by
  apply ListRecTactic
  · simp
  · simp
    apply ConsTactic
    · apply IdentityTactic
    apply NilTactic
  simp
  pushpre
  apply ConsTactic
  · apply FstTactic
    apply SndTactic
    apply IdentityTactic
  apply SndTactic
  apply SndTactic
  apply SndTactic
  apply IdentityTactic

def ReverseSolution' : ReverseProblem := by
  apply ListRecTactic'
  · apply NilTactic
  simp
  pushpre
  apply SplitTactic' (.pair .nat (.pair .list .list)) (.pair (.pair .nat .list) .list) .list
   (fun inp => ((inp.1,inp.2.1), inp.2.2)) (fun inp out => out = inp.2.append [inp.1.1])
  · apply PairTactic
    · apply PairTactic
      · apply FstTactic
        apply IdentityTactic
      apply FstTactic
      apply SndTactic
      apply IdentityTactic
    apply SndTactic
    apply SndTactic
    apply IdentityTactic
  simp
  apply ListRecTactic
  · simp
  · apply ConsTactic
    · apply FstTactic
      apply IdentityTactic
    apply NilTactic
  simp
  pushpre
  apply ConsTactic
  · apply FstTactic
    apply SndTactic
    apply IdentityTactic
  apply SndTactic
  apply SndTactic
  apply SndTactic
  apply IdentityTactic

def ConcatSolution' : ConcatProblem := by
  apply ListRecTactic
  · simp
  · apply IdentityTactic
  simp
  pushpre
  apply ConsTactic
  · apply FstTactic
    apply SndTactic
    apply IdentityTactic
  apply SndTactic
  apply SndTactic
  apply SndTactic
  apply IdentityTactic

#eval ListLanguage.Trm.pretty ReverseSolution'.code

/-! # `vericode` smoke tests

The same problems, solved automatically by the `vericode` search over the `VericodeL` rule
set — no manual guidance. `ReverseSolution''` in particular exercises the full pipeline:
`listRec` → `pushpre` → `appList` (apply an append helper to the recursive result) → `introTac`
→ nested `listRec`. -/

def UnitSolution'' : UnitProblem := by vericode
def NilSolution'' : NilProblem := by vericode
def ConsSolution'' : ConsProblem := by vericode
def NumToListSolution'' : NumToListProblem := by vericode
def List123Solution'' : List123Problem := by vericode
def AppendConstantSolution'' : AppendConstantProblem := by vericode
def AppendSolution'' : AppendProblem := by vericode
def ReverseSolution'' : ReverseProblem := by vericode
def ConcatSolution'' : ConcatProblem := by vericode

#eval ListLanguage.Trm.pretty ReverseSolution''.code
