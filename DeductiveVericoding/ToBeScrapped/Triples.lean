import Loom.MonadAlgebras.WP.Basic

universe u v

variable {m : Type u → Type v} [Monad m] [LawfulMonad m]
variable {l : Type u} [CompleteLattice l] [MAlgOrdered m l]
variable {α β : Type u}

/--
  Existential form of triple_bind.

  Given:
    - {P} c {Q}
    - ∀ y, {Q y} (f y) {R}

  We can conclude: ∃ z : m β, {P} z {R}

  The witness is `c >>= f`, the sequential composition.
-/
theorem triple_bind_exists {β} (pre : l) (x : m α) (cut : α → l)
    (f : α → m β) (post : β → l) :
    triple pre x cut →
    (∀ y, triple (cut y) (f y) post) →
    ∃ z : m β, triple pre z post := by
  intro hx hf
  exact ⟨x >>= f, triple_bind pre x cut f post hx hf⟩

/--
  Refinement type form of triple_bind.

  Given:
    - {P} c {Q}
    - ∀ y, {Q y} (f y) {R}

  We return a subtype: a computation `z : m β` refined by the proof that {P} z {R}.

  This packages the computation and its correctness proof together,
  which is more informative than a bare existential.
-/
def triple_bind_refined {β} (pre : l) (x : m α) (cut : α → l)
    (f : α → m β) (post : β → l)
    (hx : triple pre x cut)
    (hf : ∀ y, triple (cut y) (f y) post) :
    { z : m β // triple pre z post } :=
  ⟨x >>= f, triple_bind pre x cut f post hx hf⟩

/--
  Alternative: using a structure to name the components.
-/
structure RefinedComputation (m : Type u → Type v) [Monad m] (l : Type u)
    [CompleteLattice l] [MAlgOrdered m l] (β : Type u) (pre : l) (post : β → l) where
  computation : m β
  correctness : triple pre computation post

/--
  Triple bind returning a RefinedComputation structure.
-/
def triple_bind_struct {β} (pre : l) (x : m α) (cut : α → l)
    (f : α → m β) (post : β → l)
    (hx : triple pre x cut)
    (hf : ∀ y, triple (cut y) (f y) post) :
    RefinedComputation m l β pre post :=
  { computation := x >>= f
    correctness := triple_bind pre x cut f post hx hf }

/-! ## Example: Extracting a program from triple_bind_struct -/

section Example

variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable {l : Type} [CompleteLattice l] [MAlgOrdered m l]

/--
  Given assumptions `hx : {P} c {Q}` and `hf : ∀ y, {Q y} (f y) {R}`,
  we can build a refined computation and extract its program.
-/
example (P : l) (Q : Nat → l) (R : String → l)
    (c : m Nat) (f : Nat → m String)
    (hx : triple P c Q)
    (hf : ∀ y, triple (Q y) (f y) R) : m String :=
  -- Build the refined computation
  let refined := triple_bind_struct P c Q f R hx hf
  -- Extract just the program (computation)
  refined.computation

/--
  We can also extract the correctness proof separately.
-/
example (P : l) (Q : Nat → l) (R : String → l)
    (c : m Nat) (f : Nat → m String)
    (hx : triple P c Q)
    (hf : ∀ y, triple (Q y) (f y) R) : triple P (c >>= f) R :=
  let refined := triple_bind_struct P c Q f R hx hf
  refined.correctness

/--
  A more realistic example: composing two verified computations.

  Suppose we have:
  - `readInput : m Nat` with proof that it satisfies {True} readInput {λ n => n > 0}
  - `process : Nat → m String` with proof that {n > 0} process n {λ s => s.length > 0}

  We can derive a verified `readAndProcess : m String` satisfying {True} _ {λ s => s.length > 0}
-/
noncomputable def deriveVerifiedProgram
    (readInput : m Nat)
    (process : Nat → m String)
    (h_read : triple (⊤ : l) readInput (fun n => ⌜n > 0⌝))
    (h_process : ∀ n, triple (⌜n > 0⌝ : l) (process n) (fun s => ⌜s.length > 0⌝)) :
    RefinedComputation m l String ⊤ (fun s => ⌜s.length > 0⌝) :=
  triple_bind_struct ⊤ readInput (fun n => ⌜n > 0⌝) process (fun s => ⌜s.length > 0⌝)
    h_read h_process

/--
  Extract just the program from the verified derivation.
-/
noncomputable def extractProgram
    (readInput : m Nat)
    (process : Nat → m String)
    (h_read : triple (⊤ : l) readInput (fun n => ⌜n > 0⌝))
    (h_process : ∀ n, triple (⌜n > 0⌝ : l) (process n) (fun s => ⌜s.length > 0⌝)) :
    m String :=
  (deriveVerifiedProgram readInput process h_read h_process).computation

/--
  The extracted program is definitionally equal to `readInput >>= process`.
-/
example
    (readInput : m Nat)
    (process : Nat → m String)
    (h_read : triple (⊤ : l) readInput (fun n => ⌜n > 0⌝))
    (h_process : ∀ n, triple (⌜n > 0⌝ : l) (process n) (fun s => ⌜s.length > 0⌝)) :
    extractProgram readInput process h_read h_process = (readInput >>= process) :=
  rfl

end Example
