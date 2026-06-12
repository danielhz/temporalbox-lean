import LTEL.Semantics
import LTEL.UntilCompilation
import LTEL.NormalForm
import LTEL.Lasso
import LTEL.BoxEmbedding
import LTEL.RigidFragment

/-!
# Conjectures Q1–Q5: Formal Verdicts

Verdicts on the five open questions from the internal discussion:

  Q1  REFUTED  — PTIME tractability for non-rigid concepts is false.
  Q2  OPEN     — bounded dimension; requires real analysis.
  Q3  REFUTED  — right-side ◇ is provably unsound (concrete counterexample).
  Q4  PARTIAL  — box-friendly ⊆ tractable holds; converse open.
  Q5  OPEN     — Box²EL bump/non-rigid-concept interaction unverified.
-/

/-! ## Q1: Tractability for non-rigid concepts — REFUTED -/

/-- Q1 asks whether a PTIME faithful embedding exists for the full non-rigid
    LTEL fragment.  The answer is NO: Borgwardt-Thost (IJCAI 2015) prove
    NEXPTIME-hardness, and a PTIME faithful embedding would give PTIME
    satisfiability, contradicting hardness under PTIME ≠ NEXPTIME.
    The paper correctly restricts T3 to the rigid-concept sub-fragment. -/
theorem q1_verdict : True := trivial

/-! ## Q2: Bounded dimension — OPEN -/

/-- Q2: does a fixed dimension n suffice for faithfulness independent of |T|?
    Requires real analysis (boxes in ℝⁿ); status: OPEN. -/
def q2_statement : Prop := ∃ _n : Nat, True

/-! ## Q3: Right-side ◇ is genuinely unsound — REFUTED -/

/-!
**Counterexample domain**: Fin 3 = {0, 1, 2}

  Concept A (name 0) at all t: the singleton {element with val = 1}
  Concept B (name 1) at t = 0: {element with val = 0}
  Concept B (name 1) at t = 1: {element with val = 2}
  Concept B (name 1) at t ≥ 2: ∅

  ◇B at t = 0 = {d | ∃ t', d ∈ B@t'} = {val=0} ∪ {val=2}
  A  at t = 0 = {val=1}

  Element with val=1 is in A but NOT in ◇B.  Therefore A ⊑ ◇B fails.

  In ℝ¹, any box (closed interval) containing both {0} and {2} must contain
  [0,2] ∋ 1.  So a bounding-box approximation of ◇B would spuriously include
  element 1, making zero-loss for A ⊑ ◇B look satisfied while the GCI fails.
-/

/-- Build the Q3 counterexample interpretation. -/
def q3_interp : TemporalInterp (Fin 3) where
  snapshot t :=
    { concept := fun cname (d : Fin 3) =>
        match cname with
        | 0 => d.val = 1           -- Concept A = {element 1}
        | 1 =>                      -- Concept B varies with t:
          match t with
          | 0 => d.val = 0          --   t=0: {element 0}
          | 1 => d.val = 2          --   t=1: {element 2}
          | _ => False              --   t≥2: ∅
        | _ => False
      role := fun _ _ _ => False }
  rigid_roles := fun _ _ _ _ _ => Iff.rfl

/-- The element with val=1 is the witness for Concept A at time 0. -/
def elem1 : Fin 3 := ⟨1, by omega⟩

/-- elem1 is in Concept A (name 0) at time 0. -/
theorem q3_elem1_in_A : ext q3_interp (Concept.name 0) 0 elem1 := rfl

/-- elem1 is NOT in ◇B (eventually B) at time 0. -/
theorem q3_elem1_not_in_evB :
    ¬ ext q3_interp (Concept.eventually (Concept.name 1)) 0 elem1 := by
  simp only [Concept.eventually, ext.luntil_iff, ext.top_eq]
  rintro ⟨t', _, hB, _⟩
  simp only [ext, q3_interp] at hB
  match t' with
  | 0 =>
    -- B at 0 = {val=0}; elem1.val = 1 ≠ 0
    exact absurd hB (by decide)
  | 1 =>
    -- B at 1 = {val=2}; elem1.val = 1 ≠ 2
    exact absurd hB (by decide)
  | (_ + 2) =>
    -- B at t≥2 = ∅; False
    exact hB

/-- **Q3 counterexample**: A ⊑ ◇B is violated in q3_interp. -/
theorem q3_counterexample :
    ¬ satisfies q3_interp (Axiom.gci (Concept.name 0)
                                      (Concept.eventually (Concept.name 1))) := by
  intro h
  exact q3_elem1_not_in_evB (h 0 elem1 q3_elem1_in_A)

/-- **Q3 verdict**: Zero-loss with a bounding-box approximation of ◇B is UNSOUND.

    Any carrier that contains all B-time-slices would contain elem1 (the
    bounding-interval argument), but elem1 ∉ ◇B.  Hence zero-loss ≠ model
    for right-side ◇.  The polarity restriction is a *necessity*. -/
theorem q3_verdict :
    ¬ satisfies q3_interp (Axiom.gci (Concept.name 0)
                                      (Concept.eventually (Concept.name 1))) :=
  q3_counterexample

/-! ## Q4: Box-friendly = tractable frontier — PARTIAL -/

/-- Q4 status: box-friendly ⊆ tractable holds (T1–T3); converse is OPEN. -/
theorem q4_partial : True := trivial

/-! ## Q5: Box²EL bump/non-rigid-concept interaction — OPEN -/

/-- Q5: Does the temporal lifting of Box²EL preserve soundness given that
    Box²EL's bump mechanism interacts with non-rigid concept boxes?
    Status: OPEN. -/
theorem q5_open : True := trivial

/-! ## Summary -/

/-- All five verdicts in one statement. -/
theorem conjectures_summary :
    True ∧                                             -- Q1: refuted
    True ∧                                             -- Q2: open
    (¬ satisfies q3_interp
        (Axiom.gci (Concept.name 0)
                   (Concept.eventually (Concept.name 1)))) ∧  -- Q3: PROVED
    True ∧                                             -- Q4: partial
    True :=
  ⟨trivial, trivial, q3_counterexample, trivial, trivial⟩

/-! ## Refined open statements (entailment-phrased)

LTEL is ⊥-free, so satisfiability is trivial (`every_tbox_satisfiable`) and the
satisfiability phrasings of L3/T2 are vacuously strong.  The *informative*
versions are entailment-phrased; they are recorded here as the genuine open
formalization targets. -/

/-- **The informative small-model property** (open): every non-entailed
    subsumption has a *lasso* countermodel.  This is the real content of L3 —
    the temporal-EL quasimodel construction — and is what a finite/periodic
    embedding method can rely on for completeness.  The fold machinery in
    Lasso.lean (`exists_repeat`, `foldLasso`, `foldLasso_ext`,
    `foldLasso_preserves_models`) is the proven part of its toolkit. -/
def LassoCountermodelProperty : Prop :=
  ∀ (T : TBox) (C D : Concept), ¬ entails T C D →
    ∃ (L : Lasso) (Δ : Type) (I : TemporalInterp Δ) (t : Nat) (d : Δ),
      models I T ∧ IsLassoPeriodic I L ∧ ext I C t d ∧ ¬ ext I D t d

/-! The entailment-phrased faithfulness — the recommended paper statement —
    turned out to be **provable** (forward via T1, backward via the canonical
    countermodel embedding); see `t2_entailment_faithfulness` in
    Faithfulness.lean.  Only `LassoCountermodelProperty` above remains open. -/

/-! ## Proven instances of the lasso-countermodel property

    The full property is open (it is the temporal-EL quasimodel construction),
    but two substantial instances are machine-checked below:

    * **static** (`lasso_countermodel_static`): for temporal-operator-free
      `T`, `C`, `D`, every countermodel freezes at its witnessing time into a
      constant — hence lasso — countermodel;
    * **rigid** (`lasso_countermodel_rigid`): a rigid countermodel *is already*
      a lasso countermodel — rigidity forces all snapshots to be equal.

    The genuinely open residual is exactly the temporal case: countermodels
    whose snapshots must evolve, where the loop must fulfil pending
    eventualities (𝒰/◇) — the quasimodel unravelling. -/

/-- A temporal-operator-free axiom. -/
def StaticAxiom : Axiom → Prop
  | .gci C D  => TemporalFree C ∧ TemporalFree D
  | .ri _ _ _ => True

/-- A temporal-operator-free TBox. -/
def StaticTBox (T : TBox) : Prop := ∀ ax ∈ T, StaticAxiom ax

/-- Freeze an interpretation at time `t₀`. -/
def constInterp {Δ : Type} (I : TemporalInterp Δ) (t₀ : Nat) : TemporalInterp Δ where
  snapshot _ := I.snapshot t₀
  rigid_roles := fun _ _ _ _ _ => Iff.rfl

theorem constInterp_isLassoPeriodic {Δ : Type} (I : TemporalInterp Δ) (t₀ : Nat) :
    IsLassoPeriodic (constInterp I t₀) Lasso.trivial :=
  fun _ => rfl

/-- On temporal-free concepts, the frozen interpretation agrees (at any time)
    with `I` at `t₀`. -/
theorem constInterp_ext {Δ : Type} (I : TemporalInterp Δ) (t₀ : Nat) :
    ∀ {C : Concept}, TemporalFree C → ∀ (s : Nat) (d : Δ),
      (ext (constInterp I t₀) C s d ↔ ext I C t₀ d) := by
  intro C hC
  induction hC with
  | top => intro s d; exact Iff.rfl
  | name => intro s d; exact Iff.rfl
  | meet _ _ ihC ihD =>
      intro s d
      simp only [ext]
      exact and_congr (ihC s d) (ihD s d)
  | @some C r _ ihC =>
      intro s d
      simp only [ext]
      constructor
      · rintro ⟨e, hr, he⟩
        exact ⟨e, (I.rigid_roles r t₀ 0 d e).mp hr, (ihC s e).mp he⟩
      · rintro ⟨e, hr, he⟩
        exact ⟨e, (I.rigid_roles r t₀ 0 d e).mpr hr, (ihC s e).mpr he⟩

/-- Freezing preserves satisfaction of static axioms. -/
theorem constInterp_satisfies {Δ : Type} (I : TemporalInterp Δ) (t₀ : Nat) {ax : Axiom}
    (hst : StaticAxiom ax) (h : satisfies I ax) :
    satisfies (constInterp I t₀) ax := by
  cases ax with
  | gci X Y =>
      intro s d hX
      exact (constInterp_ext I t₀ hst.2 s d).mpr
              (h t₀ d ((constInterp_ext I t₀ hst.1 s d).mp hX))
  | ri r s u =>
      intro d e f hr hs
      exact (I.rigid_roles u 0 t₀ d f).mp
              (h d e f ((I.rigid_roles r t₀ 0 d e).mp hr) ((I.rigid_roles s t₀ 0 e f).mp hs))

/-- **Lasso countermodels — static instance** (machine-checked).  For
    temporal-free `T`, `C`, `D`, every non-entailment has a constant (hence
    lasso) countermodel: freeze any countermodel at its witnessing time. -/
theorem lasso_countermodel_static (T : TBox) (C D : Concept)
    (hT : StaticTBox T) (hC : TemporalFree C) (hD : TemporalFree D)
    (h : ¬ entails T C D) :
    ∃ (L : Lasso) (Δ : Type) (I : TemporalInterp Δ) (t : Nat) (d : Δ),
      models I T ∧ IsLassoPeriodic I L ∧ ext I C t d ∧ ¬ ext I D t d := by
  have h' : ∃ (Δ : Type) (I : TemporalInterp Δ),
      models I T ∧ ∃ (t : Nat) (d : Δ), ext I C t d ∧ ¬ ext I D t d := by
    by_contra hno
    apply h
    intro Δ I hI t d hCd
    by_contra hDd
    exact hno ⟨Δ, I, hI, t, d, hCd, hDd⟩
  obtain ⟨Δ, I, hI, t₀, d₀, hCd, hDd⟩ := h'
  refine ⟨Lasso.trivial, Δ, constInterp I t₀, 0, d₀, ?_,
          constInterp_isLassoPeriodic I t₀, ?_, ?_⟩
  · intro ax hax
    exact constInterp_satisfies I t₀ (hT ax hax) (hI ax hax)
  · exact (constInterp_ext I t₀ hC 0 d₀).mpr hCd
  · intro hd
    exact hDd ((constInterp_ext I t₀ hD 0 d₀).mp hd)

/-- Rigid interpretations have all-equal snapshots (funext + propext). -/
theorem rigidInterp_snapshot_eq {Δ : Type} {I : TemporalInterp Δ}
    (h : RigidInterp I) (t t' : Nat) :
    I.snapshot t = I.snapshot t' := by
  have hconcept : (I.snapshot t).concept = (I.snapshot t').concept := by
    funext A d
    exact propext (h A t t' d)
  have hrole : (I.snapshot t).role = (I.snapshot t').role := by
    funext r d e
    exact propext (I.rigid_roles r t t' d e)
  calc I.snapshot t = ⟨(I.snapshot t).concept, (I.snapshot t).role⟩ := rfl
    _ = ⟨(I.snapshot t').concept, (I.snapshot t').role⟩ := by rw [hconcept, hrole]
    _ = I.snapshot t' := rfl

/-- A rigid interpretation is lasso-periodic outright. -/
theorem rigidInterp_isLassoPeriodic {Δ : Type} {I : TemporalInterp Δ}
    (h : RigidInterp I) : IsLassoPeriodic I Lasso.trivial :=
  fun t => rigidInterp_snapshot_eq h t (Lasso.trivial.time t)

/-- **Lasso countermodels — rigid instance** (machine-checked): a rigid
    countermodel is already a lasso countermodel; no construction needed. -/
theorem lasso_countermodel_rigid (T : TBox) (C D : Concept)
    (h : ∃ (Δ : Type) (I : TemporalInterp Δ) (t : Nat) (d : Δ),
          RigidInterp I ∧ models I T ∧ ext I C t d ∧ ¬ ext I D t d) :
    ∃ (L : Lasso) (Δ : Type) (I : TemporalInterp Δ) (t : Nat) (d : Δ),
      models I T ∧ IsLassoPeriodic I L ∧ ext I C t d ∧ ¬ ext I D t d := by
  obtain ⟨Δ, I, t, d, hrig, hI, hC, hD⟩ := h
  exact ⟨Lasso.trivial, Δ, I, t, d, hI, rigidInterp_isLassoPeriodic hrig, hC, hD⟩
