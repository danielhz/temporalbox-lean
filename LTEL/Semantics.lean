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

/-! ## Entailment, and triviality of satisfiability in the ⊥-free fragment

LTEL as formalized here (and EL⁺ generally) has **no ⊥ and no negation**, so no
TBox is inconsistent: the *total* interpretation — a singleton domain where
every concept name and role holds everywhere, at every time — satisfies every
axiom.  Consequently `satisfiable T` holds for every `T`, and
satisfiability-phrased theorems are trivially true.  The informative reasoning
problem for this fragment is **entailment** (subsumption), defined below. -/

/-- T ⊨ C ⊑ D: every model of T satisfies the subsumption everywhere. -/
def entails (T : TBox) (C D : Concept) : Prop :=
  ∀ (Δ : Type) (I : TemporalInterp Δ), models I T →
    ∀ (t : Nat) (d : Δ), ext I C t d → ext I D t d

/-- The total interpretation: singleton domain, everything true everywhere. -/
def totalInterp : TemporalInterp Unit where
  snapshot _ := { concept := fun _ _ => True, role := fun _ _ _ => True }
  rigid_roles := fun _ _ _ _ _ => Iff.rfl

/-- Every concept holds everywhere in the total interpretation. -/
theorem totalInterp_ext : ∀ (C : Concept) (t : Nat) (d : Unit), ext totalInterp C t d := by
  intro C
  induction C with
  | top => intro t d; trivial
  | name A => intro t d; trivial
  | meet C D ihC ihD => intro t d; exact ⟨ihC t d, ihD t d⟩
  | some r C ihC => intro t d; exact ⟨d, trivial, ihC t d⟩
  | next C ihC => intro t d; exact ihC (t + 1) d
  | luntil C D ihC ihD =>
      intro t d
      exact ⟨t, Nat.le_refl t, ihD t d, fun t'' _ _ => ihC t'' d⟩
  | globally C ihC => intro t d t' _; exact ihC t' d

/-- The total interpretation models every TBox. -/
theorem totalInterp_models (T : TBox) : models totalInterp T := by
  intro ax _
  cases ax with
  | gci C D => intro t d _; exact totalInterp_ext D t d
  | ri r s u => intro d e f _ _; trivial

/-- **No LTEL TBox is inconsistent.**  Satisfiability is trivial in the ⊥-free
    fragment; only entailment is informative. -/
theorem every_tbox_satisfiable (T : TBox) : satisfiable T :=
  ⟨Unit, totalInterp, totalInterp_models T⟩
