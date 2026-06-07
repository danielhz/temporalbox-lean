import LTEL.Syntax

/-!
# LTEL Semantics

Temporal interpretations: sequences of classical snapshots with constant domain
and rigid roles, following Borgwardt & Thost (IJCAI 2015) and Section 2.2
of the paper.
-/

/-! ## Snapshots and temporal interpretations -/

/-- One snapshot: concept and role extensions at a single time point. -/
structure Snapshot (Δ : Type) where
  concept : ConceptName → Δ → Prop
  role    : RoleName    → Δ → Δ → Prop

/-- A temporal interpretation 𝔍 = (𝒥_t)_{t∈ℕ}: a sequence of snapshots with
    a constant domain Δ (the carrier type) and rigid roles. -/
structure TemporalInterp (Δ : Type) where
  snapshot    : Nat → Snapshot Δ
  rigid_roles : ∀ (r : RoleName) (t₁ t₂ : Nat) (d e : Δ),
                  (snapshot t₁).role r d e ↔ (snapshot t₂).role r d e

namespace TemporalInterp

/-- The (time-independent) role extension; we read it at time 0. -/
def role (I : TemporalInterp Δ) (r : RoleName) (d e : Δ) : Prop :=
  (I.snapshot 0).role r d e

end TemporalInterp

/-! ## Concept extension -/

/-- ext I C t d: element d is in the extension of concept C at time t in I.
    Structural recursion on C; the time index may grow in recursive calls
    (correct for the greatest-fixpoint semantics of □ and 𝒰). -/
def ext (I : TemporalInterp Δ) : Concept → Nat → Δ → Prop
  | .top,         _, _  => True
  | .name A,      t, d  => (I.snapshot t).concept A d
  | .meet C D,    t, d  => ext I C t d ∧ ext I D t d
  | .some r C,    t, d  => ∃ e, I.role r d e ∧ ext I C t e
  | .next C,      t, d  => ext I C (t + 1) d
  | .luntil C D,  t, d  =>
      ∃ t', t ≤ t' ∧ ext I D t' d ∧
            ∀ t'', t ≤ t'' → t'' < t' → ext I C t'' d
  | .globally C,  t, d  => ∀ t', t ≤ t' → ext I C t' d

/-! ## Satisfaction -/

/-- Satisfaction of a single axiom in interpretation I. -/
def satisfies (I : TemporalInterp Δ) : Axiom → Prop
  | .gci C D    => ∀ t d, ext I C t d → ext I D t d
  | .ri  r s u  => ∀ d e f, I.role r d e → I.role s e f → I.role u d f

/-- I is a model of TBox T (every axiom holds globally). -/
def models (I : TemporalInterp Δ) (T : TBox) : Prop :=
  ∀ ax ∈ T, satisfies I ax

/-- T is satisfiable: some model exists over some domain. -/
def satisfiable (T : TBox) : Prop :=
  ∃ (Δ : Type) (I : TemporalInterp Δ), models I T

/-! ## Basic simp lemmas -/

namespace ext

variable {Δ : Type} (I : TemporalInterp Δ)

@[simp] theorem top_eq   (t : Nat) (d : Δ) : ext I .top t d ↔ True        := Iff.rfl
@[simp] theorem meet_iff (C D : Concept) (t : Nat) (d : Δ) :
    ext I (.meet C D) t d ↔ ext I C t d ∧ ext I D t d                      := Iff.rfl
@[simp] theorem next_eq  (C : Concept) (t : Nat) (d : Δ) :
    ext I (.next C) t d ↔ ext I C (t + 1) d                                 := Iff.rfl
@[simp] theorem globally_iff (C : Concept) (t : Nat) (d : Δ) :
    ext I (.globally C) t d ↔ ∀ t', t ≤ t' → ext I C t' d                  := Iff.rfl
@[simp] theorem luntil_iff (C D : Concept) (t : Nat) (d : Δ) :
    ext I (.luntil C D) t d ↔
    ∃ t', t ≤ t' ∧ ext I D t' d ∧ ∀ t'', t ≤ t'' → t'' < t' → ext I C t'' d := Iff.rfl

/-- Eventually is Until with ⊤ on the left. -/
theorem eventually_iff (C : Concept) (t : Nat) (d : Δ) :
    ext I C.eventually t d ↔ ∃ t', t ≤ t' ∧ ext I C t' d := by
  simp only [Concept.eventually, luntil_iff, top_eq]
  constructor
  · rintro ⟨t', ht', hC, _⟩; exact ⟨t', ht', hC⟩
  · rintro ⟨t', ht', hC⟩
    exact ⟨t', ht', hC, fun _ _ _ => trivial⟩

end ext
