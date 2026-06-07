import LTEL.Semantics

/-!
# Lasso Models and the Small-Model Property (Lemma L3)

An **ultimately-periodic** (lasso) model has a finite prefix 0..k-1 and a
loop index ℓ < k: at time k the interpretation "wraps" to ℓ, so all times
t ≥ k behave like time ℓ + (t − k) mod (k − ℓ).

**L3 (Small-model property)**: if an LTEL TBox is satisfiable, it has a
lasso model.  For the rigid-concept sub-fragment the lasso length is bounded
polynomially in |T|.  For the full non-rigid fragment the bound is
non-elementary (see Conjectures.lean §Q1).
-/

/-- A lasso: prefix length k ≥ 1 and loop index ℓ < k. -/
structure Lasso where
  prefixLen : Nat
  loop      : Nat
  hLoop     : loop < prefixLen
  hPrefix   : 0 < prefixLen

namespace Lasso

/-- Map a global time t to the corresponding lasso position (in 0..k-1). -/
def time (L : Lasso) (t : Nat) : Nat :=
  if t < L.prefixLen then t
  else L.loop + (t - L.prefixLen) % (L.prefixLen - L.loop)

theorem time_lt_prefix (L : Lasso) (t : Nat) : L.time t < L.prefixLen := by
  unfold Lasso.time
  by_cases h : t < L.prefixLen
  · simp [h]
  · simp [h]
    have hd : 0 < L.prefixLen - L.loop := Nat.sub_pos_of_lt L.hLoop
    have hmod := Nat.mod_lt (t - L.prefixLen) hd
    omega

theorem time_early (L : Lasso) {t : Nat} (ht : t < L.prefixLen) : L.time t = t := by
  simp [Lasso.time, ht]

end Lasso

/-- An interpretation is lasso-periodic: snapshot t = snapshot (L.time t). -/
def IsLassoPeriodic (I : TemporalInterp Δ) (L : Lasso) : Prop :=
  ∀ t, I.snapshot t = I.snapshot (L.time t)

/-! ## L3: Small-model property -/

/-- **Lemma L3** (Small-model property, rigid-concept sub-fragment).

    A satisfiable TBox has a lasso model.  For rigid concepts the lasso
    length is at most 2^|CN| + 1, where |CN| = number of concept names in T.
    Proof: by the pigeonhole principle on the 2^|CN| possible concept-name
    extension patterns; some pattern repeats within 2^|CN| + 1 steps.

    The full proof is left sorry for the journal version. -/
theorem l3_small_model_rigid (T : TBox) (h : satisfiable T) :
    ∃ (L : Lasso) (Δ : Type) (I : TemporalInterp Δ),
      models I T ∧ IsLassoPeriodic I L :=
  sorry

/-- For the full non-rigid fragment a lasso model still exists (satisfiability
    is equivalent to lasso-satisfiability), but the lasso length may be
    non-elementarily large.  The complexity is NEXPTIME-hard (Borgwardt-Thost). -/
theorem l3_small_model_nonrigid (T : TBox) (h : satisfiable T) :
    ∃ (L : Lasso) (Δ : Type) (I : TemporalInterp Δ),
      models I T ∧ IsLassoPeriodic I L :=
  sorry
