import LTEL.RigidFragment
import LTEL.NormalForm

/-!
# Tractability (Theorem T3)

**T3**: For the rigid-concept sub-fragment, LTEL reasoning is PTIME.

The correct argument (see `RigidFragment.lean`) is a **reduction to static EL⁺**,
not an enumeration of lasso positions:

  1. When all concept names are rigid, the temporal operators collapse
     (`○A ≡ □A ≡ ◇A ≡ A`, `A 𝒰 B ≡ B`); proved as `RigidInterp.*_collapse`.
  2. Hence a rigid TBox `T` has the same models as its temporal-operator-free
     **static reduct** `T.staticReduct`, a pure EL⁺ TBox (`rigid_reduction`,
     `staticReduct_is_el`).
  3. Static EL⁺ satisfiability/subsumption is PTIME (Baader, Brandt & Lutz,
     IJCAI 2005), and the box construction is one application of the base method.

This supersedes the earlier `2^|CN|` lasso bound, which is **exponential** in
`|T|` and therefore does *not* establish PTIME (cf. @writer's note of
2026-06-09).  The complexity statement itself (PTIME) is inherited from EL⁺ and
recorded as commentary — complexity classes are not formalised here — but the
*reduction* it rests on is now machine-checked below.

**T3 does NOT extend to non-rigid concepts** (see Q1 in Conjectures.lean):
Borgwardt–Thost (IJCAI 2015) prove NEXPTIME-hardness, so a PTIME faithful
embedding for the full fragment would contradict that under PTIME ≠ NEXPTIME.
-/

/-! ## Rigid-fragment satisfiability -/

/-- **Rigid-fragment satisfiability**: `T` has a model in which every concept
    name is time-invariant (rigid).  This is the setting of the tractable
    sub-fragment.  (Replaces the previous `sorry` placeholder `IsRigidFragment`,
    which tried — incorrectly — to make rigidity a syntactic property of `T`;
    rigidity is a restriction on the admitted interpretations.) -/
def RigidSatisfiable (T : TBox) : Prop :=
  ∃ (Δ : Type) (I : TemporalInterp Δ), RigidInterp I ∧ models I T

/-! ## T3: the rigid fragment reduces to static EL⁺ -/

/-- The static reduct of a TBox is a **pure EL⁺ TBox**: every GCI has
    temporal-operator-free sides, and role inclusions are unchanged. -/
theorem staticReduct_is_el (T : TBox) :
    ∀ ax ∈ T.staticReduct,
      (∃ C D, ax = .gci C D ∧ TemporalFree C ∧ TemporalFree D) ∨
      (∃ r s u, ax = .ri r s u) := by
  intro ax hax
  obtain ⟨ax₀, _, rfl⟩ := List.mem_map.mp hax
  cases ax₀ with
  | gci C D =>
      exact Or.inl ⟨_, _, rfl, staticReduct_temporalFree C, staticReduct_temporalFree D⟩
  | ri r s u => exact Or.inr ⟨r, s, u, rfl⟩

/-- **Theorem T3** (rigid-fragment reduction — the PTIME backbone).

    Over any rigid interpretation, `T` and its static reduct have exactly the
    same models.  Combined with `staticReduct_is_el` (the reduct is pure EL⁺),
    rigid-fragment reasoning reduces to static EL⁺, which is PTIME
    (Baader–Brandt–Lutz 2005). -/
theorem t3_rigid_reduction {Δ : Type} {I : TemporalInterp Δ}
    (h : RigidInterp I) (T : TBox) :
    models I T ↔ models I T.staticReduct :=
  rigid_reduction h T

/-- Rigid-fragment satisfiability of `T` coincides with rigid satisfiability of
    its pure-EL⁺ static reduct.  This is the formal content behind "the rigid
    fragment reduces to static EL⁺". -/
theorem rigidSatisfiable_iff_staticReduct (T : TBox) :
    RigidSatisfiable T ↔
    ∃ (Δ : Type) (I : TemporalInterp Δ), RigidInterp I ∧ models I T.staticReduct := by
  constructor
  · rintro ⟨Δ, I, hrig, hI⟩; exact ⟨Δ, I, hrig, (rigid_reduction hrig T).mp hI⟩
  · rintro ⟨Δ, I, hrig, hI⟩; exact ⟨Δ, I, hrig, (rigid_reduction hrig T).mpr hI⟩

/-! ## Why T3 does not extend to non-rigid concepts -/

/-- NEXPTIME-hardness of non-rigid LTEL satisfiability
    (Borgwardt & Thost, IJCAI 2015, Theorem 4.2).  Recorded as a literature
    axiom; the reduction itself is not formalised here. -/
axiom borgwardt_thost_nexptime_hard : True

/-- A faithful PTIME construction for the full (non-rigid) fragment would yield a
    PTIME satisfiability procedure, contradicting NEXPTIME-hardness under
    PTIME ≠ NEXPTIME.  The paper therefore restricts T3 to the rigid fragment;
    this is commentary (the complexity-class argument is not formalised). -/
theorem tractability_cannot_extend_to_nonrigid : True := trivial
