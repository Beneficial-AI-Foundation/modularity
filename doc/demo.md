# Tactics-driven vericoding

## Domain specific logic

Mixed radix numbers (MRNs). Given by list of pairs of integers. It is a representation of an integer as dot product of a vector of coefficients with a vector of bases. For example, `256 = 2*100 + 5*10 + 6*1`. The bases do not need to be powers of some integer.

```
p : List (Int × Int)
```

The `eval` function gives semantics to these MRNs. It recursively computes the sum of the product of each pair.

```
def eval (p : List (Int × Int)) : Int :=
  List.foldr (fun t acc => t.1 * t.2 + acc) 0 p
```

## Refinements

Multiplication of two MRNs.

```
def mul (p q : List (Int × Int)) : List (Int × Int) :=
  List.flatMap (fun t =>
    List.map (fun t' => (t.1 * t'.1, t.2 * t'.2))
    q) p
```

Refinement using `mul`

```
@[simp] lemma eval_mul (p q : List (Int × Int)) :
  eval (mul p q) = eval p * eval q := by
  induction p with
  | nil => simp [mul, eval_nil]
  | cons t ts ih =>
    unfold mul at ih
    simp [mul, eval_cons, ih]
    ring
```

## Tactics

Suppose we want to derive base-10 multiplication. In the following example, the goal is to find an MRN whose value is the product of the values of two input MRNs.

```
example (a0 a1 b0 b1 : Int) :
  ∃ ab, eval ab = eval [(10, a1), (1, a0)] * eval [(10, b1), (1, b0)] 
```

We apply the `eval_mul` refinement

```
example (a0 a1 b0 b1 : Int) :
  ∃ ab, eval ab = eval [(10, a1), (1, a0)] * eval [(10, b1), (1, b0)] := by
  rw [←eval_mul]
```

The goal becomes

```
a0 a1 b0 b1 : ℤ
⊢ ∃ ab, eval ab = eval (mul [(10, a1), (1, a0)] [(10, b1), (1, b0)])
```

Unfortunately, there doesn't yet seem to be a tactic in Lean that can infer the `ab` metavariable from the goal by unification (i.e. trying to make two terms equal by specializing some of the variables). We need to tell Lean explicitly how to solve the equation by using `use`.

```
example (a0 a1 b0 b1 : Int) :
  ∃ ab, eval ab = eval [(10, a1), (1, a0)] * eval [(10, b1), (1, b0)] := by
  rw [←eval_mul]
  use (mul [(10, a1), (1, a0)] [(10, b1), (1, b0)])
```