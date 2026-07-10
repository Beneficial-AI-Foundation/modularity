import DeductiveVericoding.ListLanguage.Parametrized.Tactics
import DeductiveVericoding.ListLanguage.Parametrized.Translation

open ListLanguage

namespace Parametrized

abbrev ConsProblem := ImplP [] (.arrow .nat (.arrow .list .list)) (fun _ f => ∀ n, ∀ l, f n l = n :: l)

def ConsSolution : ConsProblem := by
  apply IntroPTactic _ .nat (.arrow .list .list) (fun env f => ∀ l, f l = (env.getT 0 .nat) :: l)
  apply IntroPTactic _ .list .list (fun env out => out = (env.getT 1 .nat) :: (env.getT 0 .list))
  apply ConsPTactic
  · apply ParPTactic
  apply ParPTactic

#eval Trm.pretty (toClosed ConsSolution.code)
-- "(λ x0 : Nat => (λ x1 : List => x0 :: x1))"

abbrev AppendParameterProblem := ImplP [] (.arrow .nat (.arrow .list .list)) (fun _ f => ∀ n, ∀ l, f n l = l.append [n])

def AppendParameterSolution : AppendParameterProblem := by
  apply IntroPTactic _ .nat (.arrow .list .list) (fun env f => ∀ l, f l = l.append [(env.getT 0 .nat)])
  apply ListRecPTactic _ (fun env inp out => out = inp.append [env.getT 0 Tpe.nat])
  · apply ConsPTactic
    · exact ParPTactic [Tpe.nat] Tpe.nat 0
    apply NilPTactic'
  · simp
    apply RelaxCondPTactic (t:=.list) _ (fun env out => out = (env.getT 0 .nat) :: (env.getT 2 .list))
    · apply ConsPTactic
      · apply ParPTactic
      apply ParPTactic
    intro env out h1 h2
    rw [← h2, h1]
    rfl

#eval Trm.pretty (toClosed AppendParameterSolution.code)
-- "(λ x0 : Nat => listRec((λ x1 : Unit => x0 :: []), (λ x2 : Nat => (λ x3 : List => (λ x4 : List => x2 :: x4)))))"

abbrev ReverseProblem := ImplP []  (.arrow .list .list) (fun _ f => ∀ l, f l = l.reverse)

def ReverseSolution : ReverseProblem := by
  apply ListRecPTactic _ (fun env inp out => out = inp.reverse)
  · apply NilPTactic'
  · simp
    apply RelaxCondPTactic (t:=.list) _ (fun env out => out = (env.getT 2 .list).append [env.getT 0 .nat])
    · apply AppPTactic [Tpe.nat, Tpe.list, Tpe.list] .list .list _ (fun env l out => out = l.append [env.getT 0 Tpe.nat])
      · apply ParPTactic
      apply ListRecPTactic _ (fun env inp out => out = inp.append [env.getT 0 Tpe.nat])
      · apply ConsPTactic
        · apply ParPTactic
        apply NilPTactic'
      simp
      apply RelaxCondPTactic (t:=.list) _ (fun env out => out = (env.getT 0 .nat) :: (env.getT 2 .list))
      · apply ConsPTactic
        · apply ParPTactic
        apply ParPTactic
      intro env out h1 h2
      rw [← h2, h1]
      rfl
    intro env out h1 h2
    rw [← h2, h1]
    rfl

#eval Trm.pretty (toClosed ReverseSolution.code)
-- "listRec((λ x0 : Unit => []), (λ x1 : Nat => (λ x2 : List => (λ x3 : List => listRec((λ x4 : Unit => x1 :: []), (λ x5 : Nat => (λ x6 : List => (λ x7 : List => x5 :: x7))))(x3)))))"
