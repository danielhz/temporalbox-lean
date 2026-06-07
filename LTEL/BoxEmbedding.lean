import LTEL.Semantics
import LTEL.Lasso

/-!
# Abstract Box Embedding Interface

The box geometry is abstracted through a typeclass `BoxAlgebra` capturing:

  1. **Exact meet**: carrier(b₁ ⊓ b₂) = carrier(b₁) ∩ carrier(b₂).
  2. **Monotone carrier**: b₁ ≤ b₂ ⟹ carrier(b₁) ⊆ carrier(b₂).
  3. **Top**: carrier(⊤) = whole domain.

With this interface the temporal lifting is modular over {BoxEL, ELBE,
Box²EL, TransBox}; see Conjectures.lean §Q5 for the Box²EL obligation.
-/

/-! ## Abstract box algebra -/

class BoxAlgebra (B : Type) (Δ : Type) where
  le      : B → B → Prop
  meet    : B → B → B
  carrier : B → Δ → Prop
  top     : B
  top_carrier  : ∀ d, carrier top d
  le_carrier   : ∀ b₁ b₂, le b₁ b₂ → ∀ d, carrier b₁ d → carrier b₂ d
  meet_carrier : ∀ b₁ b₂ d, carrier (meet b₁ b₂) d ↔ carrier b₁ d ∧ carrier b₂ d

/-! ## Temporal box embedding -/

/-- A temporal box embedding assigns each concept name a per-time box and
    provides a role carrier (rigid: shared across time). -/
structure TemporalBoxEmb (B Δ : Type) [BoxAlgebra B Δ] where
  conceptBox  : ConceptName → Nat → B
  roleCarrier : RoleName → Δ → Δ → Prop

/-! ## Induced temporal interpretation -/

/-- The temporal interpretation induced by a box embedding. -/
def TemporalBoxEmb.inducedInterp {B Δ : Type} [BoxAlgebra B Δ]
    (emb : TemporalBoxEmb B Δ) : TemporalInterp Δ where
  snapshot t :=
    { concept := fun A d => BoxAlgebra.carrier (emb.conceptBox A t) d
      role    := fun r d e => emb.roleCarrier r d e }
  rigid_roles := fun _ _ _ _ _ => Iff.rfl

/-! ## Zero-loss conditions -/

/-- Zero-loss for a single axiom: the induced interpretation satisfies it. -/
def ZeroLossGCI {B Δ : Type} [BoxAlgebra B Δ]
    (emb : TemporalBoxEmb B Δ) (ax : Axiom) : Prop :=
  match ax with
  | .gci C D   => ∀ t d, ext emb.inducedInterp C t d → ext emb.inducedInterp D t d
  | .ri  r s u => ∀ d e f,
      emb.inducedInterp.role r d e →
      emb.inducedInterp.role s e f →
      emb.inducedInterp.role u d f

/-- An embedding has zero loss on TBox T if every axiom has zero loss. -/
def ZeroLoss {B Δ : Type} [BoxAlgebra B Δ]
    (emb : TemporalBoxEmb B Δ) (T : TBox) : Prop :=
  ∀ ax ∈ T, ZeroLossGCI emb ax
