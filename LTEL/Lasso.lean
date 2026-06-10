import LTEL.Semantics
import Mathlib.Data.Fintype.Pigeonhole

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

/-- `time` is idempotent: it lands in the prefix, where it is the identity. -/
theorem time_idem (L : Lasso) (t : Nat) : L.time (L.time t) = L.time t :=
  L.time_early (L.time_lt_prefix t)

/-- Build a lasso from a repeated index pair `i < j`: prefix `j`, loop `i`. -/
def ofRepeat {i j : Nat} (h : i < j) : Lasso where
  prefixLen := j
  loop      := i
  hLoop     := h
  hPrefix   := Nat.lt_of_le_of_lt (Nat.zero_le i) h

end Lasso

/-! ## Pigeonhole core (Mathlib)

    The combinatorial heart of L3: any infinite sequence over a finite type
    repeats a value within `card S` steps.  This is the only place Mathlib is
    used; everything below it is core-only. -/

/-- **Pigeonhole**: an `ℕ`-indexed sequence over a finite type `S` takes the
    same value at two indices `i < j ≤ card S`. -/
theorem exists_repeat {S : Type} [Fintype S] (f : Nat → S) :
    ∃ i j, i < j ∧ j ≤ Fintype.card S ∧ f i = f j := by
  obtain ⟨a, b, hab, hfab⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt
      (fun k : Fin (Fintype.card S + 1) => f k.val)
      (by rw [Fintype.card_fin]; exact Nat.lt_succ_self _)
  have hval : a.val ≠ b.val := fun h => hab (Fin.ext h)
  rcases Nat.lt_or_ge a.val b.val with h | h
  · exact ⟨a.val, b.val, h, Nat.lt_succ_iff.mp b.isLt, hfab⟩
  · exact ⟨b.val, a.val, lt_of_le_of_ne h (Ne.symm hval),
           Nat.lt_succ_iff.mp a.isLt, hfab.symm⟩

/-- An interpretation is lasso-periodic: snapshot t = snapshot (L.time t). -/
def IsLassoPeriodic (I : TemporalInterp Δ) (L : Lasso) : Prop :=
  ∀ t, I.snapshot t = I.snapshot (L.time t)

/-! ## Folding an interpretation along a lasso (fully proved)

    Given any interpretation `I` and lasso `L`, the *fold* `I.foldLasso L`
    re-indexes time through `L.time`, collapsing the timeline onto the prefix
    `[0, prefixLen)`.  The fold is always lasso-periodic.  Rigid roles are
    preserved because the fold only reindexes snapshots.

    NB: the fold preserves periodicity unconditionally, but it does **not** in
    general preserve `models I T` — see the L3 note below. -/

/-- The fold of `I` along `L`: snapshot `t` becomes `I`'s snapshot at `L.time t`. -/
def TemporalInterp.foldLasso (I : TemporalInterp Δ) (L : Lasso) : TemporalInterp Δ where
  snapshot t := I.snapshot (L.time t)
  rigid_roles := fun r t₁ t₂ d e => I.rigid_roles r (L.time t₁) (L.time t₂) d e

/-- **The fold is always lasso-periodic.** -/
theorem foldLasso_isLassoPeriodic (I : TemporalInterp Δ) (L : Lasso) :
    IsLassoPeriodic (I.foldLasso L) L := by
  intro t
  show I.snapshot (L.time t) = I.snapshot (L.time (L.time t))
  rw [L.time_idem]

/-! ## L3: Small-model property -/

/-- **Lemma L3** (Small-model property, rigid-concept sub-fragment).

    A satisfiable TBox has a lasso model.  Standard proof: abstract each time
    point to its *type* (the set of subconcepts it realises, plus which
    eventualities are pending); the type space is finite (bounded by 2^|sub(T)|),
    so by `exists_repeat` some type recurs within 2^|sub(T)| + 1 steps, and one
    folds the model at that point (`foldLasso`) into a lasso.

    **What is proved here vs. open.**  The two structural ingredients are proved
    sorry-free above: the pigeonhole step (`exists_repeat`) and the fold into a
    lasso-periodic interpretation (`foldLasso`, `foldLasso_isLassoPeriodic`).
    The remaining obligation is `models (I.foldLasso L) T`, i.e. that the fold
    preserves satisfaction.  This is the genuine crux and is **not** discharged:

      • Local axioms (EL GCIs, role inclusions, ○) are preserved by any fold at a
        repeated snapshot, but
      • the lookahead operators □ and 𝒰 are **not** preserved by a naive fold at
        the first repeated *snapshot*.  An eventuality `A 𝒰 B` pending in the
        tail may be fulfilled only outside the chosen loop, so the type abstraction
        (not raw snapshot equality) and a fold point chosen to fulfil all pending
        eventualities within one period are required.  Formalising that
        eventuality-fulfilment argument (the temporal-EL decidability proof) is
        left open; `exists_repeat` reduced to a snapshot is deliberately **not**
        used here, because reducing to snapshot equality would be unsound for
        □/𝒰.

    For rigid concepts the lasso length is at most 2^|CN| + 1. -/
theorem l3_small_model_rigid (T : TBox) (h : satisfiable T) :
    ∃ (L : Lasso) (Δ : Type) (I : TemporalInterp Δ),
      models I T ∧ IsLassoPeriodic I L := by
  obtain ⟨Δ, I, hI⟩ := h
  -- Ingredients available: `exists_repeat` on the type sequence yields `i < j`;
  -- `Lasso.ofRepeat` builds `L`; `foldLasso_isLassoPeriodic` gives periodicity.
  -- Open: choosing the fold point so `models (I.foldLasso L) T` (eventualities).
  sorry

/-- For the full non-rigid fragment a lasso model still exists (satisfiability
    is equivalent to lasso-satisfiability), but the lasso length may be
    non-elementarily large.  The complexity is NEXPTIME-hard (Borgwardt-Thost). -/
theorem l3_small_model_nonrigid (T : TBox) (h : satisfiable T) :
    ∃ (L : Lasso) (Δ : Type) (I : TemporalInterp Δ),
      models I T ∧ IsLassoPeriodic I L :=
  sorry
