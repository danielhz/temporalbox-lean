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

/-! ## The canonical (powerset) box model

    Boxes = arbitrary subsets of Δ.  This instance witnesses that the abstract
    interface is inhabited, and (Faithfulness.lean) that **every** temporal
    interpretation is exactly representable as a zero-loss embedding — the
    substantive content of T2's forward direction. -/

instance powersetBoxAlgebra (Δ : Type) : BoxAlgebra (Δ → Prop) Δ where
  le b₁ b₂ := ∀ d, b₁ d → b₂ d
  meet b₁ b₂ := fun d => b₁ d ∧ b₂ d
  carrier b := b
  top := fun _ => True
  top_carrier := fun _ => trivial
  le_carrier := fun _ _ h => h
  meet_carrier := fun _ _ _ => Iff.rfl

/-- The canonical embedding of an interpretation: each concept name's box at
    time t is its exact extension; the role carrier is the rigid role. -/
def canonicalEmb {Δ : Type} (I : TemporalInterp Δ) : TemporalBoxEmb (Δ → Prop) Δ where
  conceptBox A t := (I.snapshot t).concept A
  roleCarrier := I.role

/-! ## Concrete axis-parallel boxes form a BoxAlgebra (grounding §3, and Q5)

    The abstract interface is realised by genuine axis-parallel box geometry in
    `α^d` (in particular ℝᵈ), not only by powerset boxes.  A box is `none`
    (the universe ⊤) or a finite `lo/hi` rectangle; meet is the coordinate-wise
    intersection and is **exact**.  This is the concept lattice shared by all
    axis-parallel box methods (BoxEL, Box²EL, TransBox).

    **Relevance to Q5 (Box²EL bump).**  Box²EL's *bump* vectors are per-concept
    parameters used only in the role/existential loss (`Box(C) ⊕ Bump(D) ⊆
    Head(r)` etc.); they are *not* part of this concept lattice.  In the temporal
    lifting they sit in the rigid role layer (here abstracted by
    `TemporalBoxEmb.roleCarrier`), while the non-rigid variation lives entirely
    in the bump-free meet/containment lattice below.  Hence the lifting's
    soundness (`t1_soundness`), which uses only this interface plus the base
    method's static ∃-soundness, is bump-agnostic — see Conjectures.lean §Q5. -/

/-- An axis-parallel box in `α^d`. -/
structure AxisBox (d : Nat) (α : Type) where
  lo : Fin d → α
  hi : Fin d → α

/-- Point membership in `[lo, hi]` coordinate-wise. -/
def AxisBox.mem {d : Nat} {α : Type} [LinearOrder α] (b : AxisBox d α) (p : Fin d → α) : Prop :=
  ∀ i, b.lo i ≤ p i ∧ p i ≤ b.hi i

/-- Carrier of an optional box (`none` = the universe ⊤). -/
def AxisBox.carrierOpt {d : Nat} {α : Type} [LinearOrder α] :
    Option (AxisBox d α) → (Fin d → α) → Prop
  | none,   _ => True
  | some b, p => b.mem p

/-- Coordinate-wise intersection (`none` is the identity). -/
def AxisBox.meetOpt {d : Nat} {α : Type} [LinearOrder α] :
    Option (AxisBox d α) → Option (AxisBox d α) → Option (AxisBox d α)
  | none,   b      => b
  | a,      none   => a
  | some a, some b => some ⟨fun i => max (a.lo i) (b.lo i), fun i => min (a.hi i) (b.hi i)⟩

/-- **Axis-parallel boxes form a `BoxAlgebra` with exact meet** — the concrete
    realisation of the §3 interface, bump-free. -/
instance axisBoxAlgebra (d : Nat) (α : Type) [LinearOrder α] :
    BoxAlgebra (Option (AxisBox d α)) (Fin d → α) where
  carrier := AxisBox.carrierOpt
  le a b := ∀ p, AxisBox.carrierOpt a p → AxisBox.carrierOpt b p
  meet := AxisBox.meetOpt
  top := none
  top_carrier := fun _ => trivial
  le_carrier := fun _ _ h => h
  meet_carrier := by
    intro a b p
    cases a with
    | none => cases b <;> simp [AxisBox.meetOpt, AxisBox.carrierOpt]
    | some a =>
        cases b with
        | none => simp [AxisBox.meetOpt, AxisBox.carrierOpt]
        | some b =>
            simp only [AxisBox.meetOpt, AxisBox.carrierOpt, AxisBox.mem]
            constructor
            · intro h
              refine ⟨fun i => ?_, fun i => ?_⟩
              · have hi := h i; rw [max_le_iff, le_min_iff] at hi; exact ⟨hi.1.1, hi.2.1⟩
              · have hi := h i; rw [max_le_iff, le_min_iff] at hi; exact ⟨hi.1.2, hi.2.2⟩
            · rintro ⟨ha, hb⟩ i
              rw [max_le_iff, le_min_iff]
              exact ⟨⟨(ha i).1, (hb i).1⟩, ⟨(ha i).2, (hb i).2⟩⟩
