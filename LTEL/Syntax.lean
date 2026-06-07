-- LTEL/Syntax.lean — imports must precede all doc-comments in Lean 4
-- (no imports needed here; this is the base module)

/-!
# LTEL Syntax

Linear Temporal EL⁺ (LTEL) concept descriptions and TBoxes.

Grammar:  C, D ::= ⊤ | A | C ⊓ D | ∃r.C | ○C | C 𝒰 D | □C
with ◇C := ⊤ 𝒰 C as an abbreviation (negation-free).
-/

/-- Concept names: natural numbers standing in for a countable set N_C. -/
abbrev ConceptName := Nat

/-- Role names: natural numbers standing in for N_R. -/
abbrev RoleName := Nat

/-- LTEL concept descriptions.
    Primitives: ⊤, concept name, meet, existential, Next (○), Until (𝒰),
    Globally (□).  Eventually (◇) is a derived operator.

    Note: the constructor is named `luntil` to avoid the reserved keyword
    `until` used by Lean 4's `repeat … until` do-notation. -/
inductive Concept : Type where
  | top      : Concept
  | name     : ConceptName → Concept
  | meet     : Concept → Concept → Concept
  | some     : RoleName → Concept → Concept
  | next     : Concept → Concept
  | luntil   : Concept → Concept → Concept   -- C 𝒰 D
  | globally : Concept → Concept             -- □C
  deriving Repr, DecidableEq

namespace Concept

/-- ◇C := ⊤ 𝒰 C  (Eventually, a negation-free abbreviation for Until). -/
def eventually (C : Concept) : Concept := luntil top C

end Concept

/-- A TBox axiom: a GCI (C ⊑ D) or a binary role inclusion (r ∘ s ⊑ t). -/
inductive Axiom : Type where
  | gci : Concept  → Concept  → Axiom
  | ri  : RoleName → RoleName → RoleName → Axiom
  deriving Repr, DecidableEq

/-- A TBox is a list of axioms (representing a finite set). -/
abbrev TBox := List Axiom
