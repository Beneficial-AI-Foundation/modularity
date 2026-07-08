import DeductiveVericoding.DoubleCat

/-!
# DoubleCodable: Verified Program Synthesis via Pseudo-Double Categories

This module reformulates the `Codable` framework using the double operadic theory
of systems (cf. Libkind-Myers, arXiv:2505.18329). We model deductive synthesis as
operations in a pseudo-double category where:

- **Objects**: Types (interfaces)
- **Vertical morphisms** (tight): Pure functions between types
- **Horizontal morphisms** (loose): Specifications (pre/post condition contracts)
- **2-cells**: Verified implementations (code + correctness proof)

This gives a compositional account of program synthesis where:
- Horizontal composition corresponds to sequential composition of specifications
- Vertical composition corresponds to refinement/abstraction
- The interchange law ensures coherent composition of verified programs

## The Double Category of Specifications

The key insight is that specifications form the horizontal morphisms of a
double category. A specification `Spec A B` from type `A` to type `B` consists of:
- A precondition `pre : A → Prop`
- A postcondition `post : A → B → Prop`

Verified implementations are 2-cells that "fill in" a square:
```
        Spec A B
    A ----------→ B
    |             |
  f |     α       | g
    ↓             ↓
    C ----------→ D
        Spec C D
```

where `α` is code + proof that transforms an implementation of `Spec A B`
(via `f` on inputs and `g` on outputs) into an implementation of `Spec C D`.
-/

namespace DoubleCodable

open Double

/-! ## Section 1: Syntax (from Function.lean) -/

/-- Runtime values: naturals or strings -/
inductive Val where
  | nat : Nat → Val
  | str : String → Val
  deriving Repr, BEq, DecidableEq

/-- Expressions: pure computations that evaluate to values -/
inductive Expr where
  | val : Val → Expr                    -- literal value
  | arg : Expr                          -- the function's input argument
  | toStr : Expr → Expr                 -- convert to string
  | append : Expr → Expr → Expr         -- string concatenation
  deriving Repr, BEq

/-- A function takes a natural number and returns an expression -/
structure Fctn where
  body : Expr
  deriving Repr, BEq

/-! ## Section 2: Evaluation -/

def Expr.eval (input : Nat) : Expr → Val
  | .val v => v
  | .arg => .nat input
  | .toStr e =>
      match e.eval input with
      | .nat n => .str (Nat.repr n)
      | .str s => .str s
  | .append e1 e2 =>
      match e1.eval input, e2.eval input with
      | .str s1, .str s2 => .str (s1 ++ s2)
      | .str s1, .nat n2 => .str (s1 ++ Nat.repr n2)
      | .nat n1, .str s2 => .str (Nat.repr n1 ++ s2)
      | .nat n1, .nat n2 => .str (Nat.repr n1 ++ Nat.repr n2)

def Fctn.eval (f : Fctn) (n : Nat) : Val := f.body.eval n

def Fctn.evalM (f : Fctn) (n : Nat) : Id Val := pure (f.body.eval n)

/-! ## Section 3: Specifications as Horizontal Morphisms

A specification from type `A` to type `B` is a contract consisting of
a precondition on inputs and a postcondition relating inputs to outputs.

In the double category of specifications:
- Objects are types
- Horizontal morphisms are specifications
- Composition of specifications uses Dijkstra-style WP composition
-/

/-- A specification from type `A` to type `B` -/
structure Spec (A B : Type*) where
  /-- Precondition on inputs -/
  pre : A → Prop
  /-- Postcondition relating inputs to outputs -/
  post : A → B → Prop

/-- Identity specification: any input is accepted, output equals input -/
def Spec.id (A : Type*) : Spec A A :=
  { pre := fun _ => True
    post := fun a b => a = b }

/-- Compose specifications: the postcondition of the first feeds into
    the precondition of the second -/
def Spec.comp {A B C : Type*} (s1 : Spec A B) (s2 : Spec B C) : Spec A C :=
  { pre := fun a => s1.pre a ∧ ∀ b, s1.post a b → s2.pre b
    post := fun a c => ∃ b, s1.post a b ∧ s2.post b c }

/-! ## Section 4: The Double Category Structure

We now define the pseudo-double category of specifications.

- **Objects**: Types (we use `Type` for simplicity)
- **Vertical morphisms**: Functions `A → B`
- **Horizontal morphisms**: Specifications `Spec A B`
- **2-cells**: Verified implementations
-/

/-- The type of objects in our double category -/
abbrev SpecObj := Type

/-- Vertical morphisms are pure functions -/
def SpecVert (A B : SpecObj) : Type := A → B

/-- Horizontal morphisms are specifications -/
def SpecHoriz (A B : SpecObj) : Type := Spec A B

/-- A 2-cell in the specification double category.

    Given vertical morphisms `f : A → C` and `g : B → D`,
    and horizontal morphisms (specs) `h : Spec A B` and `k : Spec C D`,
    a 2-cell is a proof that `f` and `g` transform implementations:

    If we have code satisfying spec `h` on input `a`,
    then applying `f` to the input and `g` to the output
    gives code satisfying spec `k`.

    ```
          h : Spec A B
      A ---------------→ B
      |                  |
    f |       cell       | g
      ↓                  ↓
      C ---------------→ D
          k : Spec C D
    ```
-/
structure SpecCell {A B C D : SpecObj}
    (f : SpecVert A C) (g : SpecVert B D)
    (h : SpecHoriz A B) (k : SpecHoriz C D) : Type where
  /-- Precondition backward transfer: k.pre ∘ f implies h.pre -/
  pre_backward : PLift (∀ a, k.pre (f a) → h.pre a)
  /-- Precondition forward transfer: h.pre implies k.pre ∘ f
      This ensures vertical composition works by providing the
      intermediate precondition needed for chaining cells. -/
  pre_forward : PLift (∀ a, h.pre a → k.pre (f a))
  /-- Postcondition transfer: h.post transfers through f, g to k.post -/
  post_transfer : PLift (∀ a b, h.pre a → h.post a b → k.post (f a) (g b))
  /-- Postcondition surjectivity: every output d of k at (f a) comes from
      some output b of h at a via g. This ensures horizontal composition
      of pre_forward works correctly. -/
  post_surj : PLift (∀ a d, h.pre a → k.post (f a) d → ∃ b, h.post a b ∧ d = g b)

/-! ## Section 5: Verified Implementations as a Module

In the Libkind-Myers framework, systems form a "loose right module" over
the double category of interactions. For our case:

- The double category has specifications as horizontal morphisms
- Verified implementations (Codable programs) form a module over it
- Composition of verified programs respects the specification structure

An implementation of a specification `Spec A B` consists of:
1. Code (in our case, `Fctn` for `A = Nat`, `B = Val`)
2. A correctness proof that the code satisfies the spec
-/

/-- A verified implementation of a specification.

    For the special case where `A = Nat` and `B = Val`, this
    corresponds to our original `Codable` type. -/
structure Implementation (s : Spec Nat Val) where
  /-- The syntactic code -/
  code : Fctn
  /-- Correctness: for all inputs satisfying the precondition,
      the output satisfies the postcondition -/
  correct : ∀ n, s.pre n → s.post n (code.eval n)

/-- An implementation is a "system" in the sense of Libkind-Myers.
    It lives over a specification (horizontal morphism) and can be
    composed with other implementations. -/
abbrev System := Implementation

/-! ## Section 6: The Codable Type as a Special Case

The original `Codable P Q` is an implementation of the specification
with precondition `P` and postcondition `Q`.
-/

/-- Convert a precondition and postcondition to a specification -/
def mkSpec (P : Nat → Prop) (Q : Nat → Val → Prop) : Spec Nat Val :=
  { pre := P, post := Q }

/-- Codable is an implementation of a specification -/
abbrev Codable (P : Nat → Prop) (Q : Nat → Val → Prop) :=
  Implementation (mkSpec P Q)

/-! ## Section 7: Horizontal Composition of Specifications

When we compose specifications horizontally, we get a notion of
"piping" the output of one spec into the input of another.

For our `Nat → Val` case, we need a way to feed `Val` back into a
computation. We model this as string concatenation.
-/

/-- Specification for string-producing computations -/
def StringSpec (f : Nat → String) : Spec Nat Val :=
  { pre := fun _ => True
    post := fun n v => v = Val.str (f n) }

/-- Horizontal composition at the level of string specifications:
    composing two string-producing specs gives a spec that concatenates -/
def StringSpec.append (f g : Nat → String) :
    Spec Nat Val := StringSpec (fun n => f n ++ g n)

/-! ## Section 8: 2-Cell Structure for Implementations

A 2-cell in the implementation module relates implementations
across specification transformations.

Given implementations of specs `s1` and `s2`, and a cell relating
the specs, we can derive relationships between implementations.
-/

/-- Transformation of implementations along a spec cell.

    If we have an implementation of `h : Spec Nat Val`,
    and a 2-cell from `h` to `k`, we can derive constraints
    on implementations of `k`. -/
structure ImplCell (h k : Spec Nat Val)
    (cell : SpecCell id id h k)
    (impl_h : Implementation h)
    (impl_k : Implementation k) where
  /-- The codes may differ, but both satisfy their specs -/
  both_correct : ∀ n, h.pre n → k.pre n →
    h.post n (impl_h.code.eval n) ∧ k.post n (impl_k.code.eval n)

/-! ## Section 9: Combinators as Operadic Composition

The `append` combinator from `Function.lean` corresponds to
horizontal composition in our module. This is the "operadic"
structure mentioned in Libkind-Myers.
-/

/-- Identity implementation: returns the input as a string -/
@[aesop safe apply (rule_sets := [Vericode])]
def showArg {P : Nat → Prop} : Codable P (fun n res => res = Val.str (Nat.repr n)) :=
  { code := ⟨.toStr .arg⟩
    correct := by intro n _; rfl }

/-- Literal string implementation -/
@[aesop safe apply (rule_sets := [Vericode])]
def str {P : Nat → Prop} (s : String) : Codable P (fun _ res => res = Val.str s) :=
  { code := ⟨.val (.str s)⟩
    correct := by intro n _; rfl }

/-- Literal nat-to-string implementation -/
@[aesop safe apply (rule_sets := [Vericode])]
def showNat {P : Nat → Prop} (m : Nat) : Codable P (fun _ res => res = Val.str (Nat.repr m)) :=
  { code := ⟨.toStr (.val (.nat m))⟩
    correct := by intro n _; rfl }

/-- Helper lemma: evaluating append of two string-producing expressions -/
theorem eval_append_str {e1 e2 : Expr} {n : Nat} {s1 s2 : String}
    (h1 : e1.eval n = Val.str s1) (h2 : e2.eval n = Val.str s2) :
    (Expr.append e1 e2).eval n = Val.str (s1 ++ s2) := by
  simp only [Expr.eval, h1, h2]

/-- Append combinator: horizontal composition of string-producing implementations.

    This is the key operadic structure: composing two systems horizontally
    using string concatenation as the wiring pattern. -/
@[aesop safe apply (rule_sets := [Vericode])]
def append {P : Nat → Prop} {x y : Nat → String}
    (r1 : Codable P (fun n res => res = Val.str (x n)))
    (r2 : Codable P (fun n res => res = Val.str (y n))) :
    Codable P (fun n res => res = Val.str (x n ++ y n)) :=
  { code := ⟨.append r1.code.body r2.code.body⟩
    correct := by
      intro n hP
      have h1 : r1.code.body.eval n = Val.str (x n) := r1.correct n hP
      have h2 : r2.code.body.eval n = Val.str (y n) := r2.correct n hP
      exact eval_append_str h1 h2 }

/-! ## Section 10: The Pseudo-Double Category Instance

We now instantiate the `PreDoubleCat` structure for specifications.
-/

/-- Vertical category structure on types with functions -/
instance : VertCat SpecObj where
  Vert := fun A B => A → B
  vId := fun _ => id
  vComp := fun f g => g ∘ f
  vComp_assoc := fun _ _ _ => rfl
  vId_comp := fun _ => rfl
  vComp_id := fun _ => rfl

/-- 2-morphisms between specifications: refinement relations (lifted to Type).
    We use `PLift` to ensure this is in `Type` rather than `Prop`.

    A refinement from s1 to s2 means s2 is "more general":
    - s2's precondition is weaker (accepts more inputs)
    - s2's postcondition, when combined with s1's precondition, implies s1's postcondition -/
structure SpecRefine {A B : SpecObj} (s1 s2 : Spec A B) : Type where
  /-- s2's precondition is weaker (more permissive) -/
  pre_weaker : PLift (∀ a, s1.pre a → s2.pre a)
  /-- Under s1's precondition, s2's postcondition implies s1's postcondition.
      This formulation allows refinements to compose properly. -/
  post_stronger : PLift (∀ a b, s1.pre a → s2.post a b → s1.post a b)

/-- Horizontal bicategory structure on types with specifications.
    Spec composition satisfies bicategory laws up to logical equivalence. -/
instance : HorizBicat SpecObj where
  Horiz := Spec
  hId := Spec.id
  hComp := Spec.comp
  Horiz₂ := fun s1 s2 => SpecRefine s1 s2
  -- Associator: (s1 ⬝ s2) ⬝ s3 → s1 ⬝ (s2 ⬝ s3)
  hAssoc := fun _ _ _ =>
    { pre_weaker := ⟨fun _ ⟨⟨h1, h12⟩, h123⟩ =>
        -- h1 : s1.pre a
        -- h12 : ∀ b, s1.post a b → s2.pre b
        -- h123 : ∀ c, (∃ b, s1.post a b ∧ s2.post b c) → s3.pre c
        -- Goal: s1.pre a ∧ ∀ b, s1.post a b → (s2.pre b ∧ ∀ c, s2.post b c → s3.pre c)
        ⟨h1, fun b hab => ⟨h12 b hab, fun c hbc => h123 c ⟨b, hab, hbc⟩⟩⟩⟩
      post_stronger := ⟨fun _ _ ⟨⟨_, h12⟩, h123⟩ ⟨b, hab, ⟨c, hbc, hcd⟩⟩ =>
        -- Input: ((s1⬝s2)⬝s3).pre a and (s1⬝(s2⬝s3)).post a d
        -- hab : s1.post a b, hbc : s2.post b c, hcd : s3.post c d
        -- Goal: ((s1⬝s2)⬝s3).post a d = ∃ c', (∃ b', s1.post a b' ∧ s2.post b' c') ∧ s3.post c' d
        ⟨c, ⟨b, hab, hbc⟩, hcd⟩⟩ }
  -- Inverse associator: s1 ⬝ (s2 ⬝ s3) → (s1 ⬝ s2) ⬝ s3
  hAssoc_inv := fun _ _ _ =>
    { pre_weaker := ⟨fun _ ⟨h1, h123⟩ =>
        -- h1 : s1.pre a
        -- h123 : ∀ b, s1.post a b → (s2.pre b ∧ ∀ c, s2.post b c → s3.pre c)
        -- Goal: (s1.pre a ∧ ∀ b, s1.post a b → s2.pre b) ∧
        --       ∀ c, (∃ b, s1.post a b ∧ s2.post b c) → s3.pre c
        ⟨⟨h1, fun b hab => (h123 b hab).1⟩,
         fun c ⟨b, hab, hbc⟩ => (h123 b hab).2 c hbc⟩⟩
      post_stronger := ⟨fun _ _ ⟨h1, h123⟩ ⟨c, ⟨b, hab, hbc⟩, hcd⟩ =>
        -- Input: (s1⬝(s2⬝s3)).pre a and ((s1⬝s2)⬝s3).post a d
        -- Goal: (s1⬝(s2⬝s3)).post a d = ∃ b', s1.post a b' ∧ (∃ c', s2.post b' c' ∧ s3.post c' d)
        ⟨b, hab, ⟨c, hbc, hcd⟩⟩⟩ }
  -- Left unitor: Spec.id ⬝ s → s
  hLeftUnitor := fun _ =>
    { pre_weaker := ⟨fun a ⟨_, h⟩ =>
        -- h : ∀ a', a = a' → s.pre a'
        h a rfl⟩
      post_stronger := ⟨fun a _ ⟨_, h⟩ hab =>
        -- Input: (Spec.id ⬝ s).pre a = True ∧ ∀ a', a = a' → s.pre a'
        -- hab : s.post a b
        -- Goal: (Spec.id ⬝ s).post a b = ∃ a', a = a' ∧ s.post a' b
        ⟨a, rfl, hab⟩⟩ }
  -- Inverse left unitor: s → Spec.id ⬝ s
  hLeftUnitor_inv := fun _ =>
    { pre_weaker := ⟨fun _ h =>
        -- h : s.pre a
        -- Goal: True ∧ ∀ a', a = a' → s.pre a'
        ⟨trivial, fun _ ha' => ha' ▸ h⟩⟩
      post_stronger := ⟨fun _ _ hpre ⟨_, ha', hpost⟩ =>
        -- Input: s.pre a and (Spec.id ⬝ s).post a b
        -- ha' : a = a', hpost : s.post a' b
        -- Goal: s.post a b
        ha' ▸ hpost⟩ }
  -- Right unitor: s ⬝ Spec.id → s
  hRightUnitor := fun _ =>
    { pre_weaker := ⟨fun _ ⟨h, _⟩ => h⟩
      post_stronger := ⟨fun _ b ⟨hpre, _⟩ hab =>
        -- Input: (s ⬝ Spec.id).pre a and s.post a b
        -- Goal: (s ⬝ Spec.id).post a b = ∃ b', s.post a b' ∧ b' = b
        ⟨b, hab, rfl⟩⟩ }
  -- Inverse right unitor: s → s ⬝ Spec.id
  hRightUnitor_inv := fun _ =>
    { pre_weaker := ⟨fun _ h =>
        -- Goal: s.pre a ∧ ∀ b, s.post a b → True
        ⟨h, fun _ _ => trivial⟩⟩
      post_stronger := ⟨fun _ _ hpre ⟨_, hpost, hb'⟩ =>
        -- Input: s.pre a and (s ⬝ Spec.id).post a b
        -- hb' : b' = b, hpost : s.post a b'
        -- Goal: s.post a b
        hb' ▸ hpost⟩ }

  -- 2-morphism category structure
  h2Id := fun _ =>
    { pre_weaker := ⟨fun _ h => h⟩
      post_stronger := ⟨fun _ _ _ hp => hp⟩ }
  h2Comp := fun r1 r2 =>
    -- r1 : SpecRefine h k, r2 : SpecRefine k m
    -- Result: SpecRefine h m
    { pre_weaker := ⟨fun a h => r2.pre_weaker.down a (r1.pre_weaker.down a h)⟩
      post_stronger := ⟨fun a b hpre mpost =>
        -- hpre : h.pre a, mpost : m.post a b
        -- Need: h.post a b
        -- Step 1: From h.pre, get k.pre via r1.pre_weaker
        let kpre := r1.pre_weaker.down a hpre
        -- Step 2: From k.pre and m.post, get k.post via r2.post_stronger
        let kpost := r2.post_stronger.down a b kpre mpost
        -- Step 3: From h.pre and k.post, get h.post via r1.post_stronger
        r1.post_stronger.down a b hpre kpost⟩ }
  h2Comp_assoc := fun _ _ _ => rfl
  h2Id_comp := fun _ => rfl
  h2Comp_id := fun _ => rfl

  -- Left whiskering: h ⊳ r for r : k → m gives (h ⬝ k) → (h ⬝ m)
  hWhiskerLeft := fun {_ _ _} (h : Spec _ _) {k m : Spec _ _} (r : SpecRefine k m) =>
    { pre_weaker := ⟨fun a ⟨hpre, hk⟩ =>
        -- hpre : h.pre a, hk : ∀ b, h.post a b → k.pre b
        -- Goal: h.pre a ∧ ∀ b, h.post a b → m.pre b
        ⟨hpre, fun b hab => r.pre_weaker.down b (hk b hab)⟩⟩
      post_stronger := ⟨fun a d ⟨hpre, hk⟩ ⟨c, hac, mcd⟩ =>
        -- hpre : h.pre a, hk : ∀ b, h.post a b → k.pre b
        -- hac : h.post a c, mcd : m.post c d
        -- Goal: ∃ c', h.post a c' ∧ k.post c' d
        let kpre := hk c hac
        let kpost := r.post_stronger.down c d kpre mcd
        ⟨c, hac, kpost⟩⟩ }
  -- Right whiskering: r ⊲ k for r : h → m gives (h ⬝ k) → (m ⬝ k)
  hWhiskerRight := fun {_ _ _} {h m : Spec _ _} (r : SpecRefine h m) (k : Spec _ _) =>
    { pre_weaker := ⟨fun a ⟨hpre, hk⟩ =>
        -- hpre : h.pre a, hk : ∀ b, h.post a b → k.pre b
        -- Goal: m.pre a ∧ ∀ b, m.post a b → k.pre b
        ⟨r.pre_weaker.down a hpre, fun b mab =>
          -- Need k.pre b from m.post a b
          -- We know h.pre a, and m.post a b
          -- By r.post_stronger: h.pre a → m.post a b → h.post a b
          let hab := r.post_stronger.down a b hpre mab
          hk b hab⟩⟩
      post_stronger := ⟨fun a d ⟨hpre, hk⟩ ⟨c, mac, kcd⟩ =>
        -- hpre : h.pre a, mac : m.post a c, kcd : k.post c d
        -- Goal: ∃ c', h.post a c' ∧ k.post c' d
        let hac := r.post_stronger.down a c hpre mac
        ⟨c, hac, kcd⟩⟩ }

  -- Isomorphism laws (hold definitionally for this representation)
  hAssoc_hAssoc_inv := fun _ _ _ => rfl
  hAssoc_inv_hAssoc := fun _ _ _ => rfl
  hLeftUnitor_hLeftUnitor_inv := fun _ => rfl
  hLeftUnitor_inv_hLeftUnitor := fun _ => rfl
  hRightUnitor_hRightUnitor_inv := fun _ => rfl
  hRightUnitor_inv_hRightUnitor := fun _ => rfl

  -- Whiskering axioms (all hold by rfl since SpecRefine is proof-irrelevant)
  hWhiskerLeft_id := fun _ _ => rfl
  hWhiskerLeft_comp := @fun _ _ _ _ _ _ _ _ _ => rfl
  hWhiskerRight_id := fun _ _ => rfl
  hWhiskerRight_comp := @fun _ _ _ _ _ _ _ _ _ => rfl
  id_hWhiskerLeft := @fun _ _ _ _ _ => rfl
  hWhiskerRight_hId := @fun _ _ _ _ _ => rfl
  hComp_hWhiskerLeft := @fun _ _ _ _ _ _ _ _ _ => rfl
  hWhiskerRight_hComp := @fun _ _ _ _ _ _ _ _ _ => rfl
  whisker_assoc := @fun _ _ _ _ _ _ _ _ _ => rfl
  whisker_exchange := @fun _ _ _ _ _ _ _ _ _ => rfl

/-- Cell structure for specifications.

    The key insight is that cells compose by chaining the transfer properties.
    The `pre_forward` field in SpecCell ensures that vertical composition works
    by providing the intermediate precondition k.pre (f a) from h.pre a. -/
instance : CellStruct SpecObj where
  Cell := fun f g h k => SpecCell f g h k

  -- Vertical composition of cells
  -- Given α : Cell f g h k and β : Cell f' g' k m
  -- Produce Cell (f' ∘ f) (g' ∘ g) h m
  vCellComp := fun {_ _ _ _ _ _} {f} {g} {_} {g'} {_} {_} {_} α β =>
    { pre_backward := ⟨fun a hm =>
        α.pre_backward.down a (β.pre_backward.down (f a) hm)⟩
      pre_forward := ⟨fun a hpre =>
        β.pre_forward.down (f a) (α.pre_forward.down a hpre)⟩
      post_transfer := ⟨fun a b hpre hpost =>
        let kpre := α.pre_forward.down a hpre
        let kpost := α.post_transfer.down a b hpre hpost
        β.post_transfer.down (f a) (g b) kpre kpost⟩
      post_surj := ⟨fun a d hpre mpost =>
        -- mpost : m.post (f' (f a)) d
        -- From β.post_surj: ∃ c, k.post (f a) c ∧ d = g' c
        let ⟨c, kpost, hd⟩ := β.post_surj.down (f a) d (α.pre_forward.down a hpre) mpost
        -- From α.post_surj: ∃ b, h.post a b ∧ c = g b
        let ⟨b, hpost, hc⟩ := α.post_surj.down a c hpre kpost
        -- So d = g' c = g' (g b) = (g' ∘ g) b
        ⟨b, hpost, hd.trans (congrArg g' hc)⟩⟩ }

  -- Horizontal composition of cells
  -- Given α : Cell f g h m and β : Cell g i k n
  -- Produce Cell f i (h ⬝ k) (m ⬝ n)
  --
  -- Note on pre_forward: Horizontal composition of pre_forward requires
  -- that outputs of m at (f a) map back to outputs of h at a via the cell.
  -- This holds for identity cells (cellHId) where f = g = id, which is
  -- the main use case for the Codable combinators.
  hCellComp := fun {_ _ _ _ _ _} {_} {g} {_} {_} {_} {_} {_} α β =>
    { pre_backward := ⟨fun a ⟨hm, hn⟩ =>
        ⟨α.pre_backward.down a hm,
         fun b hb => β.pre_backward.down b (hn (g b) (α.post_transfer.down a b (α.pre_backward.down a hm) hb))⟩⟩
      pre_forward := ⟨fun a ⟨hpre, hk⟩ =>
        -- First part: m.pre (f a) from α.pre_forward
        -- Second part: ∀ d, m.post (f a) d → n.pre d
        -- Using α.post_surj: d arises from some b via g, then use hk and β.pre_forward
        ⟨α.pre_forward.down a hpre,
         fun d mpost =>
           let ⟨b, hpost, hd⟩ := α.post_surj.down a d hpre mpost
           -- hpost : h.post a b, hd : d = g b
           let kpre := hk b hpost
           -- kpre : k.pre b, so β.pre_forward gives n.pre (g b) = n.pre d
           hd ▸ β.pre_forward.down b kpre⟩⟩
      post_transfer := ⟨fun a c hpre ⟨b, hab, hbc⟩ =>
        ⟨g b,
         α.post_transfer.down a b (And.left hpre) hab,
         β.post_transfer.down b c (hpre.right b hab) hbc⟩⟩
      post_surj := ⟨fun a d ⟨hpre, hk⟩ ⟨e, mpost, npost⟩ =>
        -- mpost : m.post (f a) e, npost : n.post e d
        -- From α.post_surj: ∃ b, h.post a b ∧ e = g b
        let ⟨b, hpost, he⟩ := α.post_surj.down a e hpre mpost
        -- From β.post_surj with k.pre b: ∃ c, k.post b c ∧ d = i c
        let kpre := hk b hpost
        let ⟨c, kpost, hd⟩ := β.post_surj.down b d kpre (he ▸ npost)
        -- So we have h.post a b, k.post b c, and d = i c
        ⟨c, ⟨b, hpost, kpost⟩, hd⟩⟩ }

  -- Identity cell on a vertical morphism f : a → b
  -- This is a cell: f f (Spec.id a) (Spec.id b)
  -- The cell boundary is:
  --     a ---id_a--→ a
  --     |           |
  --   f |   cellVId | f
  --     ↓           ↓
  --     b ---id_b--→ b
  cellVId := fun {_ _} f =>
    { pre_backward := ⟨fun _ h => h⟩   -- True → True
      pre_forward := ⟨fun _ h => h⟩    -- True → True
      post_transfer := ⟨fun _ _ _ hxy =>
        -- hxy : (Spec.id a).post x y = (x = y)
        -- Goal: (Spec.id b).post (f x) (f y) = (f x = f y)
        congrArg f hxy⟩
      post_surj := ⟨fun x _ _ hpost =>
        -- hpost : (Spec.id b).post (f x) d = (f x = d)
        -- Goal: ∃ y, (Spec.id a).post x y ∧ d = f y
        -- We need x = y and d = f y, so y = x and d = f x
        -- But hpost says f x = d, so we take y = x
        ⟨x, rfl, hpost.symm⟩⟩ }

  -- Identity cell on a horizontal morphism h : Spec a b
  -- This is a cell: id id h h
  -- Since vId = id, the transfer properties are trivial
  cellHId := fun {_ _} _ =>
    { pre_backward := ⟨fun _ hp => hp⟩
      pre_forward := ⟨fun _ hp => hp⟩
      post_transfer := ⟨fun _ _ _ hpost => hpost⟩
      post_surj := ⟨fun _ d _ hpost =>
        -- h.post a d, need ∃ b, h.post a b ∧ d = id b = b
        ⟨d, hpost, rfl⟩⟩ }

  -- Cell coherence isomorphisms
  -- These are cells with identity vertical morphisms witnessing bicategory coherence
  -- cellHAssoc : Cell id id ((h ⬝ k) ⬝ m) (h ⬝ (k ⬝ m))
  cellHAssoc := fun h k m =>
    { pre_backward := ⟨fun a ⟨hpre, hkm⟩ =>
        -- Input: (h ⬝ (k ⬝ m)).pre a
        -- Goal: ((h ⬝ k) ⬝ m).pre a
        ⟨⟨hpre, fun b hab => (hkm b hab).1⟩,
         fun c ⟨b, hab, hbc⟩ => (hkm b hab).2 c hbc⟩⟩
      pre_forward := ⟨fun a ⟨⟨hpre, hk⟩, hm⟩ =>
        -- Input: ((h ⬝ k) ⬝ m).pre a
        -- Goal: (h ⬝ (k ⬝ m)).pre a
        ⟨hpre, fun b hab => ⟨hk b hab, fun c hbc => hm c ⟨b, hab, hbc⟩⟩⟩⟩
      post_transfer := ⟨fun a d ⟨⟨_, hk⟩, hm⟩ ⟨c, ⟨b, hab, hbc⟩, hcd⟩ =>
        -- Input: ((h ⬝ k) ⬝ m).pre and ((h ⬝ k) ⬝ m).post
        -- Goal: (h ⬝ (k ⬝ m)).post a d
        ⟨b, hab, ⟨c, hbc, hcd⟩⟩⟩
      post_surj := ⟨fun a d ⟨⟨_, hk⟩, hm⟩ ⟨b, hab, ⟨c, hbc, hcd⟩⟩ =>
        -- Input: (h ⬝ (k ⬝ m)).post a d
        -- Goal: ∃ d', ((h ⬝ k) ⬝ m).post a d' ∧ d = id d'
        ⟨d, ⟨c, ⟨b, hab, hbc⟩, hcd⟩, rfl⟩⟩ }

  -- cellHLeftUnitor : Cell id id (Spec.id ⬝ h) h
  cellHLeftUnitor := fun h =>
    { pre_backward := ⟨fun a hpre =>
        ⟨trivial, fun _ ha' => ha' ▸ hpre⟩⟩
      pre_forward := ⟨fun a ⟨_, hk⟩ => hk a rfl⟩
      post_transfer := ⟨fun a b ⟨_, hk⟩ ⟨_, ha', hpost⟩ =>
        ha' ▸ hpost⟩
      post_surj := ⟨fun a d ⟨_, _⟩ hpost =>
        ⟨d, ⟨a, rfl, hpost⟩, rfl⟩⟩ }

  -- cellHRightUnitor : Cell id id (h ⬝ Spec.id) h
  cellHRightUnitor := fun h =>
    { pre_backward := ⟨fun a hpre =>
        ⟨hpre, fun _ _ => trivial⟩⟩
      pre_forward := ⟨fun a ⟨hpre, _⟩ => hpre⟩
      post_transfer := ⟨fun a b ⟨hpre, _⟩ ⟨_, hpost, hb'⟩ =>
        hb' ▸ hpost⟩
      post_surj := ⟨fun a d ⟨_, _⟩ hpost =>
        ⟨d, ⟨d, hpost, rfl⟩, rfl⟩⟩ }

  -- Inverse associator cell
  cellHAssoc_inv := fun h k m =>
    { pre_backward := ⟨fun a ⟨⟨hpre, hk⟩, hm⟩ =>
        ⟨hpre, fun b hab => ⟨hk b hab, fun c hbc => hm c ⟨b, hab, hbc⟩⟩⟩⟩
      pre_forward := ⟨fun a ⟨hpre, hkm⟩ =>
        ⟨⟨hpre, fun b hab => (hkm b hab).1⟩,
         fun c ⟨b, hab, hbc⟩ => (hkm b hab).2 c hbc⟩⟩
      post_transfer := ⟨fun a d ⟨hpre, hkm⟩ ⟨b, hab, ⟨c, hbc, hcd⟩⟩ =>
        ⟨c, ⟨b, hab, hbc⟩, hcd⟩⟩
      post_surj := ⟨fun a d ⟨hpre, hkm⟩ ⟨c, ⟨b, hab, hbc⟩, hcd⟩ =>
        ⟨d, ⟨b, hab, ⟨c, hbc, hcd⟩⟩, rfl⟩⟩ }

  -- Inverse left unitor cell: Cell id id h (Spec.id ⬝ h)
  cellHLeftUnitor_inv := fun h =>
    { pre_backward := ⟨fun a ⟨_, hk⟩ => hk a rfl⟩
      pre_forward := ⟨fun a hpre =>
        ⟨trivial, fun a' ha' => by subst ha'; exact hpre⟩⟩
      post_transfer := ⟨fun a b _ hpost =>
        ⟨a, rfl, hpost⟩⟩
      post_surj := ⟨fun a d _ ⟨w, ha', hpost⟩ =>
        -- ha' : a = w, hpost : h.post w d
        -- Goal: ∃ d', h.post a d' ∧ d = d'
        ⟨d, by subst ha'; exact hpost, rfl⟩⟩ }

  -- Inverse right unitor cell: Cell id id h (h ⬝ Spec.id)
  cellHRightUnitor_inv := fun h =>
    { pre_backward := ⟨fun a ⟨hpre, _⟩ => hpre⟩
      pre_forward := ⟨fun a hpre =>
        ⟨hpre, fun _ _ => trivial⟩⟩
      post_transfer := ⟨fun a b _ hpost =>
        ⟨b, hpost, rfl⟩⟩
      post_surj := ⟨fun a d _ ⟨b', hpost, hb'⟩ =>
        -- hpost : h.post a b', hb' : b' = d
        -- Goal: ∃ d', h.post a d' ∧ d = d'
        ⟨d, by subst hb'; exact hpost, rfl⟩⟩ }

  -- Cell coherence isomorphism inverse laws (hold by proof irrelevance of SpecCell)
  cellHAssoc_cellHAssoc_inv := fun _ _ _ => HEq.rfl
  cellHAssoc_inv_cellHAssoc := fun _ _ _ => HEq.rfl
  cellHLeftUnitor_cellHLeftUnitor_inv := fun _ => HEq.rfl
  cellHLeftUnitor_inv_cellHLeftUnitor := fun _ => HEq.rfl
  cellHRightUnitor_cellHRightUnitor_inv := fun _ => HEq.rfl
  cellHRightUnitor_inv_cellHRightUnitor := fun _ => HEq.rfl

/-- Pre-pseudo-double category instance for specifications -/
instance : PreDoubleCat SpecObj where

/-! ## Section 11: Examples

The `vericode` tactic (defined in DoubleCat.lean) automatically searches through
combinators registered with the `Vericode` rule set. The combinators `showArg`,
`str`, `showNat`, and `append` are registered above, so `vericode` can synthesize
implementations by composing them. -/

/-- Convert input to string and append "!" -/
def natToStringBang : Codable (fun _ => True) (fun n res => res = Val.str (Nat.repr n ++ "!")) := by
  vericode

/-- Always return "hello" -/
def constHello : Codable (fun _ => True) (fun _ res => res = Val.str "hello") := by
  vericode

/-- Show the number twice with a separator -/
def showTwice : Codable (fun _ => True)
    (fun n res => res = Val.str (Nat.repr n ++ "," ++ Nat.repr n)) := by
  vericode

/-! ## Section 12: Pretty Printing -/

def Val.pretty : Val → String
  | .nat n => s!"{n}"
  | .str s => s!"\"{s}\""

def Expr.pretty : Expr → String
  | .val v => v.pretty
  | .arg => "n"
  | .toStr e => s!"toString({e.pretty})"
  | .append e1 e2 => s!"{e1.pretty} ++ {e2.pretty}"

def Fctn.pretty (f : Fctn) : String := s!"fun n => {f.body.pretty}"

instance : ToString Val := ⟨Val.pretty⟩
instance : ToString Expr := ⟨Expr.pretty⟩
instance : ToString Fctn := ⟨Fctn.pretty⟩

-- Evaluate examples (these don't depend on the sorried coherence laws)
#eval natToStringBang.code.eval 42
-- Val.str "42!"

#eval natToStringBang.code.pretty
-- "fun n => toString(n) ++ \"!\""

#eval showTwice.code.eval 7
-- Val.str "7,7"

#eval showTwice.code.pretty
-- "fun n => toString(n) ++ \",\" ++ toString(n)"

/-! ## Section 13: Module Structure

The collection of implementations over specifications forms a
"loose right module" in the sense of Libkind-Myers (arXiv:2505.18329).

In their framework:
- A **double category** D has objects, horizontal morphisms (loose),
  vertical morphisms (tight), and 2-cells
- A **loose right module** M over D assigns to each object a category
  of "systems", with actions of horizontal and vertical morphisms

For our deductive synthesis case:
- D = SpecDoubleCat (objects = Types, horiz = Specs, vert = Functions)
- M = Implementation module (systems = verified code)
- The module structure captures how implementations compose

Key operations:
- `impl_id`: Identity implementation over the identity spec
- `impl_comp`: Compose implementations along spec composition
- Implementations can be acted on by 2-cells from the base category
-/

/-- The module of implementations is fibered over specifications.
    Each specification has a fiber of implementations satisfying it. -/
def ImplFiber (s : Spec Nat Val) := Implementation s

/-- Implementations form a category over each specification.
    Morphisms are refinements that preserve correctness. -/
structure ImplMorphism {s : Spec Nat Val}
    (impl1 impl2 : Implementation s) where
  /-- The codes produce the same output -/
  code_equiv : ∀ n, impl1.code.eval n = impl2.code.eval n

/-! ## Summary: The Double Operadic View of Deductive Synthesis

This module demonstrates how the Libkind-Myers double operadic framework
applies to program synthesis:

1. **The Double Category of Specifications** (SpecDoubleCat):
   - Objects: Types (Nat, Val, etc.)
   - Horizontal morphisms: Specifications `Spec A B` (pre/post contracts)
   - Vertical morphisms: Functions `A → B`
   - 2-cells: Proof transformations (SpecCell)

2. **The Module of Implementations**:
   - Over each spec, we have implementations (code + correctness proof)
   - The `append` combinator is horizontal operadic composition
   - Refinement of implementations is vertical composition

3. **Operadic Composition** (the "wiring diagram" perspective):
   - Combinators like `append`, `str`, `showArg` are operations
   - They compose implementations respecting the spec structure
   - The interchange law ensures coherent composition

This formalizes the intuition that deductive synthesis is about
filling in 2-cells (implementations) in a double category of specifications.
-/

end DoubleCodable
