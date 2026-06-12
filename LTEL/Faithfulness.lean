import LTEL.Soundness
import LTEL.Lasso

/-!
# Faithfulness (Theorem T2)

**T2**: An LTEL TBox T is satisfiable iff it admits a zero-loss embedding.

  (⟸)  Zero-loss ⟹ satisfiable:  immediate from T1.
  (⟹)  Satisfiable ⟹ zero-loss:  **representability** — any model reads
         directly as a zero-loss embedding over powerset boxes
         (`canonicalEmb`, `t2_representable`).  No lasso/L3 needed: the lasso
         matters only for *finite-dimensional concrete* boxes (ℝⁿ, cf. Q2),
         not for the abstract `BoxAlgebra` interface.

**Caveat on the statement's strength** (see `every_tbox_satisfiable`): the
⊥-free fragment has no inconsistent TBox, so *both* sides of T2 as phrased are
always true.  The informative content is (a) T1 — zero loss ⟹ the geometry is
a model — and (b) `t2_representable` — every model is *exactly* the induced
interpretation of some zero-loss embedding.  An entailment-phrased faithfulness
(box containment ⟺ entailed subsumption) is the recommended paper statement;
see Conjectures.lean §refined.
-/

variable {B Δ : Type} [BoxAlgebra B Δ]

/-! ## T2 backward direction (fully proved) -/

/-- **T2 (⟸)**: Zero-loss embedding → satisfiable. -/
theorem t2_backward (emb : TemporalBoxEmb B Δ) (T : TBox)
    (hZero : ZeroLoss emb T) :
    satisfiable T :=
  ⟨Δ, emb.inducedInterp, t1_soundness emb T hZero⟩

/-! ## T2 forward direction (proved via the canonical powerset embedding) -/

/-- Truth in the canonical embedding's induced interpretation coincides with
    truth in `I` — the embedding represents `I` *exactly*. -/
theorem canonical_ext {Δ' : Type} (I : TemporalInterp Δ') :
    ∀ (C : Concept) (t : Nat) (d : Δ'),
      ext (canonicalEmb I).inducedInterp C t d ↔ ext I C t d := by
  intro C
  induction C with
  | top => intro t d; exact Iff.rfl
  | name A => intro t d; exact Iff.rfl
  | meet C D ihC ihD =>
      intro t d
      simp only [ext]
      exact and_congr (ihC t d) (ihD t d)
  | some r C ihC =>
      intro t d
      simp only [ext]
      constructor
      · rintro ⟨e, hr, he⟩; exact ⟨e, hr, (ihC t e).mp he⟩
      · rintro ⟨e, hr, he⟩; exact ⟨e, hr, (ihC t e).mpr he⟩
  | next C ihC =>
      intro t d
      simp only [ext]
      exact ihC (t + 1) d
  | luntil C D ihC ihD =>
      intro t d
      simp only [ext]
      constructor
      · rintro ⟨t', ht', hD, hC⟩
        exact ⟨t', ht', (ihD t' d).mp hD, fun t'' h1 h2 => (ihC t'' d).mp (hC t'' h1 h2)⟩
      · rintro ⟨t', ht', hD, hC⟩
        exact ⟨t', ht', (ihD t' d).mpr hD, fun t'' h1 h2 => (ihC t'' d).mpr (hC t'' h1 h2)⟩
  | globally C ihC =>
      intro t d
      simp only [ext]
      constructor
      · intro hall t' ht'; exact (ihC t' d).mp (hall t' ht')
      · intro hall t' ht'; exact (ihC t' d).mpr (hall t' ht')

/-- **Representability**: the canonical embedding of `I` has zero loss on `T`
    exactly when `I` models `T`.  This is the substantive content of T2's
    forward direction — every model is exactly a zero-loss embedding. -/
theorem t2_representable {Δ' : Type} (I : TemporalInterp Δ') (T : TBox) :
    ZeroLoss (canonicalEmb I) T ↔ models I T := by
  constructor
  · intro h ax hax
    have hz := h ax hax
    cases ax with
    | gci C D =>
        intro t d hC
        exact (canonical_ext I D t d).mp (hz t d ((canonical_ext I C t d).mpr hC))
    | ri r s u => exact hz
  · intro h ax hax
    have hs := h ax hax
    cases ax with
    | gci C D =>
        intro t d hC
        exact (canonical_ext I D t d).mpr (hs t d ((canonical_ext I C t d).mp hC))
    | ri r s u => exact hs

/-- **T2 (⟹)**: Satisfiable → zero-loss embedding exists — via representability
    of the witnessing model.  (NB: `satisfiable T` is in fact always true in the
    ⊥-free fragment, `every_tbox_satisfiable`; the representability theorem
    above is the informative statement.) -/
theorem t2_forward (T : TBox) (hSat : satisfiable T) :
    ∃ (B' Δ' : Type) (_ : BoxAlgebra B' Δ') (emb : TemporalBoxEmb B' Δ'),
      ZeroLoss emb T := by
  obtain ⟨Δ', I, hI⟩ := hSat
  exact ⟨Δ' → Prop, Δ', inferInstance, canonicalEmb I, (t2_representable I T).mpr hI⟩

/-! ## T2 full faithfulness theorem -/

/-- **Theorem T2** (Faithfulness): satisfiable ↔ zero-loss embedding. -/
theorem t2_faithfulness (T : TBox) :
    satisfiable T ↔
    ∃ (B' Δ' : Type) (_ : BoxAlgebra B' Δ') (emb : TemporalBoxEmb B' Δ'),
      ZeroLoss emb T := by
  constructor
  · exact t2_forward T
  · rintro ⟨B', Δ', inst, emb, hZ⟩
    exact t2_backward emb T hZ

/-! ## Generic lifting theorem -/

/-- **Faithfulness transfers** from the static base method.

    If the static base method is faithful (characterised by its own abstract
    interface), the temporal lifting is also faithful.  This justifies applying
    the construction to any provably faithful member of the box-embedding family. -/
theorem faithfulness_transfers
    (_baseMethodFaithful :
      ∀ T_static : TBox,
        satisfiable T_static ↔
        ∃ (B' Δ' : Type) (_ : BoxAlgebra B' Δ') (emb : TemporalBoxEmb B' Δ'),
          ZeroLoss emb T_static)
    (T : TBox) :
    satisfiable T ↔
    ∃ (B' Δ' : Type) (_ : BoxAlgebra B' Δ') (emb : TemporalBoxEmb B' Δ'),
      ZeroLoss emb T :=
  t2_faithfulness T

/-- Specialisation to the BoxEL base method (Xiong et al., ISWC 2022),
    whose static faithfulness is an established theorem. -/
theorem t2_boxel (T : TBox)
    (_boxelFaithful :
      ∀ T_el : TBox,
        satisfiable T_el ↔
        ∃ (B' Δ' : Type) (_ : BoxAlgebra B' Δ') (emb : TemporalBoxEmb B' Δ'),
          ZeroLoss emb T_el) :
    satisfiable T ↔
    ∃ (B' Δ' : Type) (_ : BoxAlgebra B' Δ') (emb : TemporalBoxEmb B' Δ'),
      ZeroLoss emb T :=
  t2_faithfulness T

/-! ## Entailment-phrased faithfulness (the informative T2) -/

/-- **Entailment faithfulness** — the recommended phrasing of T2 for the ⊥-free
    fragment, where satisfiability is trivial: `T ⊨ C ⊑ D` iff every zero-loss
    embedding's induced interpretation satisfies `C ⊑ D`.
    Forward: induced interpretations of zero-loss embeddings are models (T1).
    Backward: a countermodel interpretation yields a zero-loss *countermodel
    embedding* via `canonicalEmb` + `t2_representable`. -/
theorem t2_entailment_faithfulness (T : TBox) (C D : Concept) :
    entails T C D ↔
    (∀ (B' Δ' : Type) (_ : BoxAlgebra B' Δ') (emb : TemporalBoxEmb B' Δ'),
       ZeroLoss emb T →
       ∀ t d, ext emb.inducedInterp C t d → ext emb.inducedInterp D t d) := by
  constructor
  · intro hent B' Δ' inst emb hzl t d hC
    exact hent Δ' emb.inducedInterp (t1_soundness emb T hzl) t d hC
  · intro hbox Δ' I hI t d hC
    have h := hbox (Δ' → Prop) Δ' inferInstance (canonicalEmb I)
                ((t2_representable I T).mpr hI) t d ((canonical_ext I C t d).mpr hC)
    exact (canonical_ext I D t d).mp h
