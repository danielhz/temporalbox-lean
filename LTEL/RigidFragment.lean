import LTEL.Semantics

/-!
# Rigid Fragment: temporal collapse and reduction to static EL⁺

When all concept names have time-invariant extensions ("rigid"), the temporal
operators collapse:

  ○A ≡ □A ≡ ◇A ≡ A,   and   A 𝒰 B ≡ B.

Consequently a rigid LTEL TBox is equivalent (over rigid interpretations) to its
temporal-operator-free **static reduct**, a pure EL⁺ TBox.  This is the correct
basis for the rigid-fragment tractability claim (T3): reasoning reduces to static
EL⁺, which is PTIME (Baader et al., 2005) — *not* an enumeration of `2^|CN|`
lasso positions, which would be exponential.
-/

variable {Δ : Type}

/-- An interpretation is **rigid** when every concept name has a time-invariant
    extension. -/
def RigidInterp (I : TemporalInterp Δ) : Prop :=
  ∀ (A : ConceptName) (t t' : Nat) (d : Δ),
    (I.snapshot t).concept A d ↔ (I.snapshot t').concept A d

namespace RigidInterp

variable {I : TemporalInterp Δ}

/-- In a rigid interpretation **every** concept's extension is time-invariant. -/
theorem ext_time_invariant (h : RigidInterp I) :
    ∀ (C : Concept) (t t' : Nat) (d : Δ), ext I C t d ↔ ext I C t' d := by
  intro C
  induction C with
  | top => intro t t' d; exact Iff.rfl
  | name A => intro t t' d; exact h A t t' d
  | meet C D ihC ihD =>
      intro t t' d
      show (ext I C t d ∧ ext I D t d) ↔ (ext I C t' d ∧ ext I D t' d)
      exact and_congr (ihC t t' d) (ihD t t' d)
  | some r C ihC =>
      intro t t' d
      constructor
      · rintro ⟨e, hr, hC⟩; exact ⟨e, hr, (ihC t t' e).mp hC⟩
      · rintro ⟨e, hr, hC⟩; exact ⟨e, hr, (ihC t' t e).mp hC⟩
  | next C ihC =>
      intro t t' d
      show ext I C (t + 1) d ↔ ext I C (t' + 1) d
      exact ihC (t + 1) (t' + 1) d
  | luntil C D _ ihD =>
      intro t t' d
      constructor
      · rintro ⟨s, _, hD, _⟩
        exact ⟨t', Nat.le_refl t', (ihD s t' d).mp hD,
               fun u hu hlt => absurd hlt (Nat.not_lt.mpr hu)⟩
      · rintro ⟨s, _, hD, _⟩
        exact ⟨t, Nat.le_refl t, (ihD s t d).mp hD,
               fun u hu hlt => absurd hlt (Nat.not_lt.mpr hu)⟩
  | globally C ihC =>
      intro t t' d
      constructor
      · intro hall s _; exact (ihC t s d).mp (hall t (Nat.le_refl t))
      · intro hall s _; exact (ihC t' s d).mp (hall t' (Nat.le_refl t'))

/-! ## Temporal collapse (answers the Q1 note: ○A ≡ □A ≡ ◇A ≡ A) -/

/-- ○C ≡ C under rigidity. -/
theorem next_collapse (h : RigidInterp I) (C : Concept) (t : Nat) (d : Δ) :
    ext I (.next C) t d ↔ ext I C t d :=
  h.ext_time_invariant C (t + 1) t d

/-- □C ≡ C under rigidity. -/
theorem globally_collapse (h : RigidInterp I) (C : Concept) (t : Nat) (d : Δ) :
    ext I (.globally C) t d ↔ ext I C t d := by
  constructor
  · intro hall; exact hall t (Nat.le_refl t)
  · intro hC s _; exact (h.ext_time_invariant C t s d).mp hC

/-- C 𝒰 D ≡ D under rigidity. -/
theorem luntil_collapse (h : RigidInterp I) (C D : Concept) (t : Nat) (d : Δ) :
    ext I (.luntil C D) t d ↔ ext I D t d := by
  constructor
  · rintro ⟨s, _, hD, _⟩; exact (h.ext_time_invariant D s t d).mp hD
  · intro hD
    exact ⟨t, Nat.le_refl t, hD, fun u hu hlt => absurd hlt (Nat.not_lt.mpr hu)⟩

/-- ◇C ≡ C under rigidity. -/
theorem eventually_collapse (h : RigidInterp I) (C : Concept) (t : Nat) (d : Δ) :
    ext I C.eventually t d ↔ ext I C t d :=
  h.luntil_collapse .top C t d

end RigidInterp

/-! ## Static reduct: strip the temporal operators -/

/-- The **static reduct** of a concept: remove every temporal operator
    (`○C ↦ C`, `□C ↦ C`, `C 𝒰 D ↦ D`).  Sound under rigidity (see
    `staticReduct_ext`). -/
def staticReduct : Concept → Concept
  | .top        => .top
  | .name A     => .name A
  | .meet C D   => .meet (staticReduct C) (staticReduct D)
  | .some r C   => .some r (staticReduct C)
  | .next C     => staticReduct C
  | .globally C => staticReduct C
  | .luntil _ D => staticReduct D

/-- Concepts free of all temporal operators (pure EL⁺). -/
inductive TemporalFree : Concept → Prop where
  | top  : TemporalFree .top
  | name : TemporalFree (.name A)
  | meet : TemporalFree C → TemporalFree D → TemporalFree (.meet C D)
  | some : TemporalFree C → TemporalFree (.some r C)

/-- The static reduct is always temporal-operator-free. -/
theorem staticReduct_temporalFree : ∀ C, TemporalFree (staticReduct C) := by
  intro C
  induction C with
  | top => exact .top
  | name A => exact .name
  | meet C D ihC ihD => exact .meet ihC ihD
  | some r C ihC => exact .some ihC
  | next C ihC => exact ihC
  | globally C ihC => exact ihC
  | luntil C D _ ihD => exact ihD

/-- **Static reduct preserves extension under rigidity.** -/
theorem staticReduct_ext {I : TemporalInterp Δ} (h : RigidInterp I) :
    ∀ (C : Concept) (t : Nat) (d : Δ),
      (ext I (staticReduct C) t d ↔ ext I C t d) := by
  intro C
  induction C with
  | top => intro t d; exact Iff.rfl
  | name A => intro t d; exact Iff.rfl
  | meet C D ihC ihD =>
      intro t d
      show (ext I (staticReduct C) t d ∧ ext I (staticReduct D) t d) ↔ _
      exact and_congr (ihC t d) (ihD t d)
  | some r C ihC =>
      intro t d
      show (∃ e, I.role r d e ∧ ext I (staticReduct C) t e) ↔ _
      constructor
      · rintro ⟨e, hr, hC⟩; exact ⟨e, hr, (ihC t e).mp hC⟩
      · rintro ⟨e, hr, hC⟩; exact ⟨e, hr, (ihC t e).mpr hC⟩
  | next C ihC =>
      intro t d
      show ext I (staticReduct C) t d ↔ _
      rw [ihC t d]; exact (h.next_collapse C t d).symm
  | globally C ihC =>
      intro t d
      show ext I (staticReduct C) t d ↔ _
      rw [ihC t d]; exact (h.globally_collapse C t d).symm
  | luntil C D _ ihD =>
      intro t d
      show ext I (staticReduct D) t d ↔ _
      rw [ihD t d]; exact (h.luntil_collapse C D t d).symm

/-! ## TBox-level reduction -/

/-- Static reduct of an axiom (temporal operators stripped from both sides of a
    GCI; role inclusions are already temporal-operator-free). -/
def Axiom.staticReduct : Axiom → Axiom
  | .gci C D  => .gci (_root_.staticReduct C) (_root_.staticReduct D)
  | .ri r s u => .ri r s u

/-- Static reduct of a TBox. -/
def TBox.staticReduct (T : TBox) : TBox := T.map Axiom.staticReduct

/-- A single axiom's static reduct is satisfied iff the axiom is, under rigidity. -/
theorem satisfies_staticReduct {I : TemporalInterp Δ} (h : RigidInterp I) (ax : Axiom) :
    satisfies I ax.staticReduct ↔ satisfies I ax := by
  cases ax with
  | gci C D =>
      constructor
      · intro hsat t d hC
        exact (staticReduct_ext h D t d).mp
                (hsat t d ((staticReduct_ext h C t d).mpr hC))
      · intro hsat t d hC
        exact (staticReduct_ext h D t d).mpr
                (hsat t d ((staticReduct_ext h C t d).mp hC))
  | ri r s u => exact Iff.rfl

/-- **Rigid reduction**: over a rigid interpretation, a TBox and its static
    reduct have exactly the same models.  The static reduct is a pure EL⁺ TBox
    (`staticReduct_temporalFree`), so rigid-fragment reasoning reduces to static
    EL⁺. -/
theorem rigid_reduction {I : TemporalInterp Δ} (h : RigidInterp I) (T : TBox) :
    models I T ↔ models I T.staticReduct := by
  constructor
  · intro hI ax hax
    -- ax ∈ T.staticReduct = T.map Axiom.staticReduct
    obtain ⟨ax₀, hax₀, rfl⟩ := List.mem_map.mp hax
    exact (satisfies_staticReduct h ax₀).mpr (hI ax₀ hax₀)
  · intro hI ax hax
    exact (satisfies_staticReduct h ax).mp
            (hI ax.staticReduct (List.mem_map.mpr ⟨ax, hax, rfl⟩))
