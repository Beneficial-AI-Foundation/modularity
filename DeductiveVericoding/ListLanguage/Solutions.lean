import DeductiveVericoding.ListLanguage.Problems
import DeductiveVericoding.ListLanguage.Tactics

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
  apply SplitTactic (.pair .nat (.pair .list .list)) (.pair (.pair .nat .list) .list) .list
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
