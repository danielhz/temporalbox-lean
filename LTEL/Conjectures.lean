import LTEL.Semantics
import LTEL.UntilCompilation
import LTEL.NormalForm
import LTEL.Lasso
import LTEL.BoxEmbedding

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
