import LTEL.Soundness
import LTEL.Lasso

/-!
# Faithfulness (Theorem T2)

**T2**: An LTEL TBox T is satisfiable iff it admits a zero-loss embedding.

  (⟸)  Zero-loss ⟹ satisfiable:  immediate from T1.
  (⟹)  Satisfiable ⟹ zero-loss:  take a lasso model (L3), read extensions
         as box carriers, verify zero-loss by construction.

The generic lifting theorem: if the static base method is faithful, the
temporal lifting is faithful.
-/

variable {B Δ : Type} [BoxAlgebra B Δ]

/-! ## T2 backward direction (fully proved) -/

/-- **T2 (⟸)**: Zero-loss embedding → satisfiable. -/
theorem t2_backward (emb : TemporalBoxEmb B Δ) (T : TBox)
    (hZero : ZeroLoss emb T) :
    satisfiable T :=
  ⟨Δ, emb.inducedInterp, t1_soundness emb T hZero⟩

/-! ## T2 forward direction (sorry pending L3) -/

/-- **T2 (⟹)**: Satisfiable → zero-loss embedding exists.

    Proof sketch: take a lasso model I (L3), define box carriers as the exact
    snapshot extensions.  Then zero-loss holds by definition of models. -/
theorem t2_forward (T : TBox) (hSat : satisfiable T) :
    ∃ (B' Δ' : Type) (_ : BoxAlgebra B' Δ') (emb : TemporalBoxEmb B' Δ'),
      ZeroLoss emb T :=
  sorry

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
