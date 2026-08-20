import DeductiveVericoding.ListLanguage.Basic
import DeductiveVericoding.ListLanguage.Tactics

open ListLanguage

def last : List Nat → Nat
  | [] => 0
  | [a] => a
  | _ :: l => last l

def AppendSpec : Nat × List Nat → List Nat → Prop := fun ⟨a, l⟩ out => List.Perm (a :: l) out ∧ last out = a

abbrev AppendProblem_hard := Impl (.pair .nat .list) .list (fun _ => true) AppendSpec

theorem AppendSpec_empty (a : Nat) (l : List Nat) : AppendSpec (a, []) l ↔ l = [a] := by
  simp [AppendSpec]
  aesop

theorem AppendSpec_cons (a b : Nat) (l1 l2 : List Nat) (h : AppendSpec (a, l1) l2) : AppendSpec (a, b :: l1) (b :: l2) := by
  induction l2
  · simp_all [AppendSpec]
  exact ⟨by grind [AppendSpec], h.2⟩

theorem AppendSpec_cons' (a b : Nat) (l1 l2 l3: List Nat) (h : AppendSpec (a, l1) l2) (h2 : l3 = b :: l2) : AppendSpec (a, b :: l1) l3 :=
  h2 ▸ AppendSpec_cons a b l1 l2 h

def AppendSolution_hard : AppendProblem_hard := by
  vericode [AppendSpec_cons', AppendSpec_empty]
