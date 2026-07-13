import DeductiveVericoding.ListLanguage.Parametrized.Tactics
import DeductiveVericoding.ListLanguage.Parametrized.Translation

open ListLanguage

namespace Parametrized

abbrev ConsProblem := ImplP [] (.arrow .nat (.arrow .list .list)) (fun _ f => ∀ n, ∀ l, f n l = n :: l)

def ConsSolution : ConsProblem := by
  introP
  introP
  apply ConsPTactic
  · apply ParPTactic
  apply ParPTactic

#eval Trm.pretty (toClosed ConsSolution.code)
-- "(λ x0 : Nat => (λ x1 : List => x0 :: x1))"

abbrev AppendParameterProblem := ImplP [] (.arrow .nat (.arrow .list .list)) (fun _ f => ∀ n, ∀ l, f n l = l.append [n])

def AppendParameterSolution : AppendParameterProblem := by
  introP
  listRecP
  · apply ConsPTactic
    · exact ParPTactic [Tpe.nat] Tpe.nat 0
    apply NilPTactic'
  · simp
    pushpreP
    apply ConsPTactic
    · apply ParPTactic
    apply ParPTactic

#eval Trm.pretty (toClosed AppendParameterSolution.code)
-- "(λ x0 : Nat => listRec((λ x1 : Unit => x0 :: []), (λ x2 : Nat => (λ x3 : List => (λ x4 : List => x2 :: x4)))))"

abbrev ReverseProblem := ImplP []  (.arrow .list .list) (fun _ f => ∀ l, f l = l.reverse)

def ReverseSolution : ReverseProblem := by
  listRecP
  · apply NilPTactic'
  · simp
    pushpreP
    apply AppPTactic [Tpe.nat, Tpe.list, Tpe.list] .list .list _ (fun env l out => out = l.append [env.getT 0 Tpe.nat])
    · apply ParPTactic
    listRecP
    · apply ConsPTactic
      · apply ParPTactic
      apply NilPTactic'
    simp
    pushpreP
    apply ConsPTactic
    · apply ParPTactic
    apply ParPTactic

#eval Trm.pretty (toClosed ReverseSolution.code)
-- "listRec((λ x0 : Unit => []), (λ x1 : Nat => (λ x2 : List => (λ x3 : List => listRec((λ x4 : Unit => x1 :: []), (λ x5 : Nat => (λ x6 : List => (λ x7 : List => x5 :: x7))))(x3)))))"

/-- Regression test for the `introP` macro: it infers `s`, `t` and the residual condition
    from the goal, including the de Bruijn shift when introducing under an existing parameter.
    Note that `introP` is invoked with no explicit arguments at all. -/
example : ImplP [] (.arrow .nat (.arrow .list .list)) (fun _ f => ∀ n, ∀ l, f n l = n :: l) := by
  introP -- infers s = .nat, t = .arrow .list .list, Cond = fun e out => ∀ l, out l = e.getT 0 .nat :: l
  introP -- infers s = .list, t = .list, shifting the earlier lookup to `e.getT 1 .nat`
  apply ConsPTactic
  · apply ParPTactic
  apply ParPTactic
