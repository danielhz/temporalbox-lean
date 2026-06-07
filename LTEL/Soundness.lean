import LTEL.BoxEmbedding
import LTEL.UntilCompilation

/-!
# Soundness (Theorem T1)

Zero-loss ⟹ all temporal subsumptions of T hold in the induced interpretation.
-/

variable {B Δ : Type} [BoxAlgebra B Δ]

/-! ## T1: Soundness via ZeroLossGCI definition -/

/-- **Theorem T1** (Soundness): zero-loss ⟹ model. -/
theorem t1_soundness (emb : TemporalBoxEmb B Δ) (T : TBox)
    (hZero : ZeroLoss emb T) :
    models emb.inducedInterp T :=
  fun ax hax => hZero ax hax

/-! ## T1 for each normal-form GCI shape

    Concept-name parameters are named `cA`, `cB`, etc. to avoid shadowing
    the `B : Type` box-type variable in the module `variable` header. -/

/-- T1 for NF-EL1 (cA ⊑ cB). -/
theorem t1_nf1 (emb : TemporalBoxEmb B Δ) (cA cB : ConceptName)
    (hle : ∀ (t : Nat) (d : Δ),
      BoxAlgebra.carrier (emb.conceptBox cA t) d →
      BoxAlgebra.carrier (emb.conceptBox cB t) d) :
    ∀ (t : Nat) (d : Δ),
      ext emb.inducedInterp (.name cA) t d →
      ext emb.inducedInterp (.name cB) t d := by
  intro t d hA
  simp only [ext, TemporalBoxEmb.inducedInterp] at hA ⊢
  exact hle t d hA

/-- T1 for NF-EL2 (cA₁ ⊓ cA₂ ⊑ cB). -/
theorem t1_nf2 (emb : TemporalBoxEmb B Δ) (cA₁ cA₂ cB : ConceptName)
    (hle : ∀ (t : Nat) (d : Δ),
      BoxAlgebra.carrier (emb.conceptBox cA₁ t) d →
      BoxAlgebra.carrier (emb.conceptBox cA₂ t) d →
      BoxAlgebra.carrier (emb.conceptBox cB t) d) :
    ∀ (t : Nat) (d : Δ),
      ext emb.inducedInterp (.meet (.name cA₁) (.name cA₂)) t d →
      ext emb.inducedInterp (.name cB) t d := by
  intro t d ⟨hA₁, hA₂⟩
  simp only [ext, TemporalBoxEmb.inducedInterp] at hA₁ hA₂ ⊢
  exact hle t d hA₁ hA₂

/-- T1 for NF-T1 (cA ⊑ ○cB): box(○cB, t) = box(cB, t+1). -/
theorem t1_next (emb : TemporalBoxEmb B Δ) (cA cB : ConceptName)
    (hle : ∀ (t : Nat) (d : Δ),
      BoxAlgebra.carrier (emb.conceptBox cA t) d →
      BoxAlgebra.carrier (emb.conceptBox cB (t + 1)) d) :
    ∀ (t : Nat) (d : Δ),
      ext emb.inducedInterp (.name cA) t d →
      ext emb.inducedInterp (.next (.name cB)) t d := by
  intro t d hA
  simp only [ext.next_eq, ext, TemporalBoxEmb.inducedInterp] at hA ⊢
  exact hle t d hA

/-- T1 for NF-T3 (cA ⊑ □cB): greatest-fixpoint meet covers all t' ≥ t. -/
theorem t1_globally (emb : TemporalBoxEmb B Δ) (cA cB : ConceptName)
    (hle : ∀ (t t' : Nat) (d : Δ), t ≤ t' →
      BoxAlgebra.carrier (emb.conceptBox cA t) d →
      BoxAlgebra.carrier (emb.conceptBox cB t') d) :
    ∀ (t : Nat) (d : Δ),
      ext emb.inducedInterp (.name cA) t d →
      ext emb.inducedInterp (.globally (.name cB)) t d := by
  intro t d hA t' ht'
  simp only [ext, TemporalBoxEmb.inducedInterp] at hA ⊢
  exact hle t t' d ht' hA

/-- T1 for NF-T4 (cA 𝒰 cB ⊑ cC): compiled away by L2; no box for 𝒰. -/
theorem t1_until (emb : TemporalBoxEmb B Δ) (cA cB cC : ConceptName)
    (hFamily : ∀ (t t' : Nat) (d : Δ),
       t ≤ t' →
       ext emb.inducedInterp (.name cB) t' d →
       (∀ t'', t ≤ t'' → t'' < t' → ext emb.inducedInterp (.name cA) t'' d) →
       ext emb.inducedInterp (.name cC) t d) :
    ∀ (t : Nat) (d : Δ),
      ext emb.inducedInterp (.luntil (.name cA) (.name cB)) t d →
      ext emb.inducedInterp (.name cC) t d := by
  rw [l2_until_compilation]
  exact hFamily
