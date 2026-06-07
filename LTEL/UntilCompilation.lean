import LTEL.Semantics

/-!
# Left-Side Until Compilation (Lemma L2)

A GCI of the form  (A 𝒰 B) ⊑ C  is semantically equivalent to an infinite
family of pointwise containments indexed by witness times t' ≥ t:

  ∀ t t' d,  t ≤ t'  →  d ∈ B^{t'}  →  (∀ t'' ∈ [t,t'), d ∈ A^{t''})  →  d ∈ C^t.

Over a lasso (finite ultimately-periodic model) this family is finite, so each
𝒰-on-left GCI unfolds into at most k containment constraints — one per lasso
position.  Crucially, **no box is ever constructed for 𝒰 itself**.
-/

variable {Δ : Type} (I : TemporalInterp Δ)

/-! ## L2: Until compilation (fully proved) -/

/-- **Lemma L2** (Left-side Until compilation).

    The global GCI `(C 𝒰 D) ⊑ E` holds iff for every witness time t' ≥ t
    and every d satisfying D at t' and C at all t'' in [t, t'), d ∈ E at t.

    **This proof is complete (no sorry).** -/
theorem l2_until_compilation (C D E : Concept) :
    (∀ t d, ext I (.luntil C D) t d → ext I E t d) ↔
    (∀ t t' d,
       t ≤ t' →
       ext I D t' d →
       (∀ t'', t ≤ t'' → t'' < t' → ext I C t'' d) →
       ext I E t d) := by
  constructor
  · intro hGCI t t' d ht' hD hC
    apply hGCI
    exact ⟨t', ht', hD, hC⟩
  · intro hFamily t d hUntil
    obtain ⟨t', ht', hD, hC⟩ := hUntil
    exact hFamily t t' d ht' hD hC

/-- **Corollary**: t-local version of L2. -/
theorem l2_until_compilation_local (C D E : Concept) (t : Nat) :
    (∀ d, ext I (.luntil C D) t d → ext I E t d) ↔
    (∀ t' d,
       t ≤ t' → ext I D t' d →
       (∀ t'', t ≤ t'' → t'' < t' → ext I C t'' d) →
       ext I E t d) := by
  constructor
  · intro h t' d ht' hD hC; apply h; exact ⟨t', ht', hD, hC⟩
  · intro h d ⟨t', ht', hD, hC⟩;  exact h t' d ht' hD hC

/-! ## Why right-side 𝒰/◇ is excluded -/

/-- The existential-witness form of right-side Until (for reference).
    Any box carrying `C 𝒰 D` on the RHS would need to represent the *union*
    ⋃_{t'≥t}(D@t' ∩ ⋂_{t≤t''<t'} C@t''), which is generally NOT a single
    axis-aligned box.  See Conjectures.lean §Q3 for the formal impossibility. -/
theorem rhs_until_is_existential (C D : Concept) (t : Nat) (d : Δ) :
    ext I (.luntil C D) t d ↔
    ∃ t', t ≤ t' ∧ ext I D t' d ∧ ∀ t'', t ≤ t'' → t'' < t' → ext I C t'' d :=
  ext.luntil_iff I C D t d
