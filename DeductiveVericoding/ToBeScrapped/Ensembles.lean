/- Naive Set Theory in Lean 4 -/
import Aesop

namespace Ensembles

variable {U : Type}

/-- An ensemble is a predicate on elements of type U -/
def Ensemble (U : Type) := U → Prop

/-- Membership in an ensemble -/
@[simp] def In {U : Type} (A : Ensemble U) (x : U) : Prop := A x

/-- Set inclusion -/
@[simp] def Included {U : Type} (B C : Ensemble U) : Prop := ∀ x : U, In B x → In C x

/-- Empty set -/
inductive Empty_set {U : Type} : Ensemble U where

/-- Full set containing all elements -/
inductive Full_set {U : Type} : Ensemble U where
  | full_intro (x : U) : Full_set x

/-- Singleton set containing exactly one element -/
inductive Singleton {U : Type} (x : U) : Ensemble U where
  | in_singleton : Singleton x x

/-- Union of two sets -/
@[aesop safe [constructors, cases]]
inductive Union {U : Type} (B C : Ensemble U) : Ensemble U where
  | union_introl : ∀ x : U, B x → Union B C x
  | union_intror : ∀ x : U, C x → Union B C x

/-- Add an element to a set -/
@[simp] def Add {U : Type} (B : Ensemble U) (x : U) : Ensemble U := Union B (Singleton x)

/-- Intersection of two sets -/
@[aesop safe [constructors, cases]]
inductive Intersection {U : Type} (B C : Ensemble U) : Ensemble U where
  | intersection_intro : ∀ x : U, B x → C x → Intersection B C x

/-- Set containing exactly two elements -/
@[aesop safe [constructors, cases]]
inductive Couple {U : Type} (x y : U) : Ensemble U where
  | couple_l : Couple x y x
  | couple_r : Couple x y y

/-- Set containing exactly three elements -/
@[aesop safe [constructors, cases]]
inductive Triple {U : Type} (x y z : U) : Ensemble U where
  | triple_l : Triple x y z x
  | triple_m : Triple x y z y
  | triple_r : Triple x y z z

/-- Complement of a set -/
def Complement {U : Type} (A : Ensemble U) : Ensemble U := fun x : U => ¬In A x

/-- Set difference -/
@[simp] def Setminus {U : Type} (B C : Ensemble U) : Ensemble U :=
  fun x : U => In B x ∧ ¬In C x

/-- Remove an element from a set -/
@[simp] def Subtract {U : Type} (B : Ensemble U) (x : U) : Ensemble U := Setminus B (Singleton x)

/-- Disjoint sets -/
@[aesop safe [constructors, cases]]
inductive Disjoint {U : Type} (B C : Ensemble U) : Prop where
  | disjoint_intro : (∀ x : U, ¬In (Intersection B C) x) → Disjoint B C

/-- Inhabited set -/
inductive Inhabited {U : Type} (B : Ensemble U) : Prop where
  | inhabited_intro : ∀ x : U, In B x → Inhabited B

/-- Strict inclusion -/
@[simp] def Strict_Included {U : Type} (B C : Ensemble U) : Prop := Included B C ∧ B ≠ C

/-- Set equality -/
@[simp] def Same_set {U : Type} (B C : Ensemble U) : Prop := Included B C ∧ Included C B

/-- Extensionality Axiom -/
@[simp] axiom Extensionality_Ensembles {U : Type} : ∀ A B : Ensemble U, Same_set A B → A = B

end Ensembles
