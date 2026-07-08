import Mathlib.Data.Set.Basic
import Mathlib.Data.Prod.Basic

namespace Fiat

/-- Return a value into a computation -/
def Return {A : Type} (a : A) : Set A := {a}

/-- Bind two computations together -/
def Bind {A B : Type} (ca : Set A) (k : A → Set B) : Set B :=
  { b | ∃ a, a ∈ ca ∧ b ∈ k a }

/-- Pick a value from a set satisfying a predicate -/
def Pick {A : Type} (P : Set A) : Set A := P

/-- Bind two values from a pair computation -/
def Bind2 {A B C : Type} (c : Set (A × B)) (k : A → B → Set C) : Set C :=
  Bind c (fun ab => k ab.1 ab.2)

/-- Notation for Return -/
notation "ret" => Return

/-- Notation for Bind -/
infixl:81 " >>= " => Bind

/-- Notation for sequential bind -/
syntax (priority := high) "do" term " <- " term " ; " term : term
macro_rules
  | `(do $x <- $ca; $k) => `(Bind $ca (fun $x => $k))

/-- Notation for sequential composition -/
infixl:81 " >> " => fun x z => Bind x (fun _ => z)

/-- Notation for Pick -/
notation "{ " x " | " P " }" => Pick (fun x => P)
notation "{ " x " : " A " | " P " }" => @Pick A (fun x => P)

/-- Computes to relation -/
def computes_to {A : Type} (ca : Set A) (a : A) : Prop := a ∈ ca

/-- Notation for computes_to -/
infix:50 " ↝ " => computes_to

/-- Return computes to its value -/
theorem ReturnComputes {A : Type} (a : A) : ret a ↝ a := by
  exact Set.mem_singleton a

/-- Unfold computes_to definition -/
theorem unfold_computes {A : Type} (c : Set A) (a : A) : c ↝ a ↔ a ∈ c := by
  rfl

/-- Bind computes to its result -/
theorem BindComputes {A B : Type} (ca : Set A) (f : A → Set B) (a : A) (b : B)
    (h1 : ca ↝ a) (h2 : f a ↝ b) : ca >>= f ↝ b := by
  exists a
  constructor
  · exact h1
  · exact h2

/-- Pick computes to a value satisfying the predicate -/
theorem PickComputes {A : Type} (P : Set A) (a : A) (h : a ∈ P) : {a' | a' ∈ P} ↝ a := by
  exact h

/-- Return inverse -/
theorem Return_inv {A : Type} (a v : A) (h : ret a ↝ v) : a = v := by
  exact Set.mem_singleton_iff.mp h

/-- Bind inverse -/
theorem Bind_inv {A B : Type} (ca : Set A) (f : A → Set B) (v : B)
    (h : ca >>= f ↝ v) : ∃ a', ca ↝ a' ∧ f a' ↝ v := by
  exact h

/-- Pick inverse -/
theorem Pick_inv {A : Type} (P : Set A) (v : A) (h : {a | a ∈ P} ↝ v) : v ∈ P := by
  exact h

/-- Refinement relation -/
def refine {A : Type} (old new : Set A) : Prop :=
  ∀ v, new ↝ v → old ↝ v

/-- Refinement type -/
def Refinement_Of {A : Type} (c : Set A) :=
  { c' : Set A // refine c c' }

/-- Notation for Refinement_Of -/
notation "Refinement of " c => Refinement_Of c

/-- Symmetrized refinement -/
def refineEquiv {A : Type} (old new : Set A) : Prop :=
  refine old new ∧ refine new old

/-- Refinement is a preorder -/
instance refine_PreOrder (A : Type) : Preorder (@refine A) where
  refl := by
    intro x v h
    exact h
  trans := by
    intro x y z h1 h2 v h3
    exact h1 v (h2 v h3)

/-- Refinement equivalence is an equivalence relation -/
instance refineEquiv_Equivalence (A : Type) : Equivalence (@refineEquiv A) where
  refl := by
    intro x
    constructor <;> exact fun v h => h
  symm := by
    intro x y h
    constructor <;> exact h.2 <;> exact h.1
  trans := by
    intro x y z h1 h2
    constructor
    · intro v h3
      exact h1.1 v (h2.1 v h3)
    · intro v h3
      exact h2.2 v (h1.2 v h3)

end Fiat 