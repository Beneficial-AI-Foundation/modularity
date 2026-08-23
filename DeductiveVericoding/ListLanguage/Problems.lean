import DeductiveVericoding.ListLanguage.Basic

open ListLanguage

/-
Here we have a collection of vericoding Problems in the List language defined in ListLanguage.lean.

This file holds only the *specifications*; the implementations that meet them live in
`Solutions.lean`.
-/

abbrev UnitProblem := Impl .unit .unit (fun _ => True) (fun _ out => out = ())

abbrev NilProblem := Impl .unit .list (fun _ => True) (fun _ out => out = [])

abbrev ConsProblem := Impl (.pair .nat .list) .list (fun _ => True) (fun ⟨x, xs⟩ out => out = x :: xs)

abbrev NumToListProblem := Impl .nat .list (fun _ => True) (fun x out => out = [x])

abbrev List123Problem := Impl .unit .list (fun _ => True) (fun _ out => out = [1,2,3])

abbrev AppendConstantProblem := Impl .list .list (fun _ => True) (fun inp out => out = inp.append [1])

abbrev AppendProblem := Impl (.pair .nat .list) .list (fun _ => True) (fun ⟨a, l⟩ out => out = l.append [a])

abbrev ReverseProblem := Impl .list .list (fun _ => True) (fun l out => out = l.reverse)

abbrev ConcatProblem := Impl (.pair .list .list) .list (fun _ => True) (fun ⟨l1, l2⟩ out => out = l2.append l1)

/-- The larger of two numbers. Stated as a predicate rather than as `out = …` so that solving it
requires *deciding* something: the implementation has to compare `x` and `y`. (The argument order
keeps `out` off the end, so the postcondition below does not eta-reduce to a partial application,
which nothing could unfold.) -/
def MaxSpec (out x y : Nat) : Prop := out = if x ≤ y then y else x

abbrev MaxProblem := Impl (.pair .nat .nat) .nat (fun _ => True) (fun p out => MaxSpec out p.1 p.2)

abbrev IsEmptyProblem := Impl .list .bool (fun _ => True) (fun inp out => out = inp.isEmpty)
