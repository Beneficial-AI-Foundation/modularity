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
  sorry

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

#eval ListLanguage.Trm.pretty ConcatSolution'.code
