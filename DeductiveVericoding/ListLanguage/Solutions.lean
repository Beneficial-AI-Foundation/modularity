import DeductiveVericoding.ListLanguage.Problems
import DeductiveVericoding.ListLanguage.Tactics

def UnitSolution' : UnitProblem := by
  apply UnitTactic

def NilSolution' : NilProblem := by
  apply NilTactic

def ConsSolution' : ConsProblem := by
  apply ConsTactic
  · apply FstTactic
  apply SndTactic

def NumToListSolution' : NumToListProblem := by
  apply ConsTactic
  · apply IdentityTactic
  apply NilTactic

def List123Solution' : List123Problem := by
  apply ConsTactic
  · apply NumTactic
  apply ConsTactic
  · apply NumTactic
  apply ConsTactic
  · apply NumTactic
  apply NilTactic

def AppendConstantSolution' : AppendConstantProblem := by
  apply ListRecTactic'
  ·

def AppendSolution' : AppendProblem := by
  apply ListRecTactic
  · simp
    apply NumToListSolution'
  simp
  sorry

def ReverseSolution' : ReverseProblem := by
  apply ListRecTactic'
  · apply NilTactic
  simp
  sorry

def ConcatSolution' : ConcatProblem := sorry
