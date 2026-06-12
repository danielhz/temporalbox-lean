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

/-- `time L.prefixLen = L.loop`: the first wrap lands on the loop index. -/
theorem time_prefixLen (L : Lasso) : L.time L.prefixLen = L.loop := by
  simp only [Lasso.time, lt_irrefl, if_false, Nat.sub_self, Nat.zero_mod, Nat.add_zero]

/-- **Successor homomorphism**: the lasso position of `t+1` is the position
    reached by stepping once from the position of `t`.  This is what makes the
    Next (○) operator commute with the fold. -/
theorem time_succ (L : Lasso) (t : Nat) :
    L.time (t + 1) = L.time (L.time t + 1) := by
  rcases Nat.lt_or_ge t L.prefixLen with ht | ht
  · -- t < prefixLen: time t = t, both sides reduce to L.time (t+1)
    rw [L.time_early ht]
  · -- t ≥ prefixLen
    have hℓ : L.loop < L.prefixLen := L.hLoop
    have hd : 0 < L.prefixLen - L.loop := Nat.sub_pos_of_lt hℓ
    have hge1 : ¬ (t < L.prefixLen) := Nat.not_lt.mpr ht
    have hge2 : ¬ (t + 1 < L.prefixLen) := by omega
    have hrlt : (t - L.prefixLen) % (L.prefixLen - L.loop) < L.prefixLen - L.loop :=
      Nat.mod_lt _ hd
    have htime_t : L.time t = L.loop + (t - L.prefixLen) % (L.prefixLen - L.loop) := by
      simp only [Lasso.time, if_neg hge1]
    have hle : L.time t + 1 ≤ L.prefixLen := by rw [htime_t]; omega
    have hdm := Nat.div_add_mod (t - L.prefixLen) (L.prefixLen - L.loop)
    rcases Nat.lt_or_eq_of_le hle with hcase | hcase
    · -- no wrap: time t + 1 < prefixLen
      have hrlt' : (t - L.prefixLen) % (L.prefixLen - L.loop) + 1 < L.prefixLen - L.loop := by
        have h := hcase; rw [htime_t] at h; omega
      have hval : (t + 1 - L.prefixLen) % (L.prefixLen - L.loop)
          = (t - L.prefixLen) % (L.prefixLen - L.loop) + 1 := by
        rw [show t + 1 - L.prefixLen
              = ((t - L.prefixLen) % (L.prefixLen - L.loop) + 1)
                + (L.prefixLen - L.loop) * ((t - L.prefixLen) / (L.prefixLen - L.loop))
            from by omega,
           Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrlt']
      rw [L.time_early hcase, htime_t]
      simp only [Lasso.time, if_neg hge2, hval, Nat.add_assoc]
    · -- wrap: time t + 1 = prefixLen
      have hrdd : (t - L.prefixLen) % (L.prefixLen - L.loop) + 1 = L.prefixLen - L.loop := by
        have h := hcase; rw [htime_t] at h; omega
      have hval0 : (t + 1 - L.prefixLen) % (L.prefixLen - L.loop) = 0 := by
        rw [show t + 1 - L.prefixLen
              = (L.prefixLen - L.loop)
                + (L.prefixLen - L.loop) * ((t - L.prefixLen) / (L.prefixLen - L.loop))
            from by omega,
           Nat.add_mul_mod_self_left, Nat.mod_self]
      rw [hcase, L.time_prefixLen]
      simp only [Lasso.time, if_neg hge2, hval0, Nat.add_zero]

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

/-- The fold leaves the (rigid) role extension unchanged. -/
theorem foldLasso_role (I : TemporalInterp Δ) (L : Lasso) (r : RoleName) (d e : Δ) :
    (I.foldLasso L).role r d e = I.role r d e := by
  show (I.snapshot (L.time 0)).role r d e = (I.snapshot 0).role r d e
  rw [L.time_early L.hPrefix]

/-! ## The fold preserves the eventuality-free fragment (fully proved)

    Folding preserves satisfaction for the fragment **without** □ and 𝒰
    (`BoxUntilFree`), provided the loop is *good*: truth of every box/until-free
    concept agrees at the loop index and at the prefix length.  This is the exact
    boundary of what folding can achieve — see the L3 note below for why □/𝒰
    cannot be added. -/

/-- Concepts free of the lookahead operators □ and 𝒰. -/
inductive BoxUntilFree : Concept → Prop where
  | top  : BoxUntilFree .top
  | name : BoxUntilFree (.name A)
  | meet : BoxUntilFree C → BoxUntilFree D → BoxUntilFree (.meet C D)
  | some : BoxUntilFree C → BoxUntilFree (.some r C)
  | next : BoxUntilFree C → BoxUntilFree (.next C)

/-- A loop is *good* for `I` when truth of every box/until-free concept agrees at
    the loop index and at the prefix length.  This is exactly the wrap-around
    coherence the Next operator needs. -/
def GoodLoop (I : TemporalInterp Δ) (L : Lasso) : Prop :=
  ∀ C, BoxUntilFree C → ∀ d, (ext I C L.loop d ↔ ext I C L.prefixLen d)

/-- **Substitution lemma**: on the box/until-free fragment, truth in the fold at
    time `t` equals truth in `I` at the folded time `L.time t`. -/
theorem foldLasso_ext (I : TemporalInterp Δ) (L : Lasso) (hgood : GoodLoop I L) :
    ∀ {C : Concept}, BoxUntilFree C → ∀ (t : Nat) (d : Δ),
      (ext (I.foldLasso L) C t d ↔ ext I C (L.time t) d) := by
  intro C hC
  induction hC with
  | top => intro t d; exact Iff.rfl
  | name => intro t d; exact Iff.rfl
  | meet _ _ ihC ihD =>
      intro t d
      exact and_congr (ihC t d) (ihD t d)
  | @some r C _ ihC =>
      intro t d
      constructor
      · rintro ⟨e, hr, hC'⟩
        exact ⟨e, by rwa [foldLasso_role] at hr, (ihC t e).mp hC'⟩
      · rintro ⟨e, hr, hC'⟩
        exact ⟨e, by rw [foldLasso_role]; exact hr, (ihC t e).mpr hC'⟩
  | @next C hC ihC =>
      intro t d
      show ext (I.foldLasso L) C (t + 1) d ↔ ext I C (L.time t + 1) d
      rw [ihC (t + 1) d, L.time_succ t]
      have hle1 : L.time t + 1 ≤ L.prefixLen := L.time_lt_prefix t
      rcases Nat.lt_or_eq_of_le hle1 with hlt | heq
      · rw [L.time_early hlt]
      · rw [heq, L.time_prefixLen]
        exact hgood C hC d

/-- A single axiom is in the box/until-free fragment. -/
def AxBoxUntilFree : Axiom → Prop
  | .gci C D  => BoxUntilFree C ∧ BoxUntilFree D
  | .ri _ _ _ => True

/-- A TBox is in the box/until-free fragment. -/
def TBoxBoxUntilFree (T : TBox) : Prop := ∀ ax ∈ T, AxBoxUntilFree ax

/-- **The fold preserves models on the eventuality-free fragment**, given a good
    loop.  (For □/𝒰 this is false — see the L3 note.) -/
theorem foldLasso_preserves_models (I : TemporalInterp Δ) (L : Lasso)
    (hgood : GoodLoop I L) (T : TBox) (hbf : TBoxBoxUntilFree T) (hI : models I T) :
    models (I.foldLasso L) T := by
  intro ax hax
  cases ax with
  | gci C D =>
      obtain ⟨hbC, hbD⟩ := hbf _ hax
      intro t d hC
      have hCI : ext I C (L.time t) d := (foldLasso_ext I L hgood hbC t d).mp hC
      exact (foldLasso_ext I L hgood hbD t d).mpr (hI _ hax (L.time t) d hCI)
  | ri r s u =>
      intro d e f hr hs
      rw [foldLasso_role] at hr hs ⊢
      exact hI _ hax d e f hr hs

/-! ## L3: Small-model property -/

/-- The trivial lasso: prefix length 1, loop at 0 — constant interpretations
    are lasso-periodic for it. -/
def Lasso.trivial : Lasso := ⟨1, 0, Nat.zero_lt_one, Nat.zero_lt_one⟩

/-- The total interpretation is (trivially) lasso-periodic: it is constant. -/
theorem totalInterp_isLassoPeriodic : IsLassoPeriodic totalInterp Lasso.trivial :=
  fun _ => rfl

/-- **Lemma L3** (Small-model property, satisfiability phrasing) — **proved,
    but the statement is weaker than it looks.**

    As stated — "a satisfiable TBox has a lasso model" — this is trivially true,
    for a reason that is itself a finding about the logic: LTEL has **no ⊥ and
    no negation**, so *every* TBox is satisfiable (`every_tbox_satisfiable`),
    and the constant total interpretation is a lasso model of everything.  The
    satisfiability phrasing of the small-model property therefore carries no
    information in this fragment.

    The **informative** small-model property is about *countermodels to
    non-entailed subsumptions*: if `¬ entails T C D`, is there a *lasso*
    countermodel?  That statement (`LassoCountermodelProperty`, see
    Conjectures.lean) is the genuine quasimodel construction and remains open;
    the fold machinery above (`exists_repeat`, `foldLasso`, `foldLasso_ext`,
    `foldLasso_preserves_models`) is the proven part of its toolkit, and the
    two obstructions documented there (folding cannot manufacture periodicity;
    □/𝒰 break the substitution lemma) are why it needs the full
    type/quasimodel unravelling. -/
theorem l3_small_model_rigid (T : TBox) (_h : satisfiable T) :
    ∃ (L : Lasso) (Δ : Type) (I : TemporalInterp Δ),
      models I T ∧ IsLassoPeriodic I L :=
  ⟨Lasso.trivial, Unit, totalInterp, totalInterp_models T, totalInterp_isLassoPeriodic⟩

/-- Non-rigid case of the satisfiability phrasing: same triviality (the total
    interpretation is in particular rigid, hence also a non-rigid model). -/
theorem l3_small_model_nonrigid (T : TBox) (_h : satisfiable T) :
    ∃ (L : Lasso) (Δ : Type) (I : TemporalInterp Δ),
      models I T ∧ IsLassoPeriodic I L :=
  ⟨Lasso.trivial, Unit, totalInterp, totalInterp_models T, totalInterp_isLassoPeriodic⟩
