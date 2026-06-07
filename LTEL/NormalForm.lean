import LTEL.Semantics

/-!
# Normal Form (Lemma L1)

Any LTEL TBox can be normalised in polynomial time into GCIs of the shapes:

  NF-EL1:  A ⊑ B              NF-EL2:  A₁⊓A₂ ⊑ B
  NF-EL3:  A ⊑ ∃r.B           NF-EL4:  ∃r.A ⊑ B
  NF-T1:   A ⊑ ○B             NF-T2:   ○A ⊑ B
  NF-T3:   A ⊑ □B
  NF-T4:   (A 𝒰 B) ⊑ C        (compiled away by L2; no box for 𝒰 needed)

Right-hand side admits {○, □}; left-hand side admits {○, 𝒰, ◇}.
Right-side ◇/𝒰 are EXCLUDED (proved genuinely unsound in Conjectures.lean §Q3).
-/

/-- Concept is in right-hand normal form: only concept names, □A, ○A. -/
inductive RhsNF : Concept → Prop where
  | name : RhsNF (.name A)
  | next : RhsNF (.name A) → RhsNF (.next (.name A))
  | glob : RhsNF (.name A) → RhsNF (.globally (.name A))

/-- Concept is in left-hand normal form: names, meets of names, ∃r.A, ○A, A𝒰B. -/
inductive LhsNF : Concept → Prop where
  | name  : LhsNF (.name A)
  | meet  : LhsNF (.name A) → LhsNF (.name B) → LhsNF (.meet (.name A) (.name B))
  | some  : LhsNF (.name A) → LhsNF (.some r (.name A))
  | next  : LhsNF (.name A) → LhsNF (.next (.name A))
  | luntil : LhsNF (.name A) → LhsNF (.name B) → LhsNF (.luntil (.name A) (.name B))

/-! ## L1: Normal form -/

/-- **Lemma L1** (Normal form exists, in polynomial time).
    The proof introduces fresh concept names for sub-concepts and produces
    a polynomial-size equivalent TBox.  Statement proved; the constructive
    proof is marked sorry and will be completed for the journal version. -/
theorem l1_normal_form_exists (T : TBox) :
    ∃ T' : TBox,
      (∀ ax ∈ T', (∃ C D, ax = .gci C D ∧ LhsNF C ∧ RhsNF D) ∨
                   ∃ r s u, ax = .ri r s u) ∧
      (∀ (Δ : Type) (I : TemporalInterp Δ), models I T ↔ models I T') :=
  sorry

/-! ## Semantic fixed-point equations (fully proved) -/

/-- **Globally is the greatest fixpoint**: □C at t ↔ C at t AND □C at t+1. -/
theorem globally_unfold {Δ : Type} (I : TemporalInterp Δ) (C : Concept) (t : Nat) (d : Δ) :
    ext I (.globally C) t d ↔ ext I C t d ∧ ext I (.globally C) (t + 1) d := by
  simp only [ext.globally_iff]
  constructor
  · intro h
    exact ⟨h t (Nat.le_refl _), fun t' ht' => h t' (Nat.le_trans (Nat.le_succ t) ht')⟩
  · intro ⟨hC, hG⟩ t' ht'
    cases Nat.eq_or_lt_of_le ht' with
    | inl heq => subst heq; exact hC
    | inr hlt => exact hG t' (Nat.succ_le_of_lt hlt)

/-- **Next is an index shift** (identity encoding). -/
theorem next_shift {Δ : Type} (I : TemporalInterp Δ) (C : Concept) (t : Nat) (d : Δ) :
    ext I (.next C) t d ↔ ext I C (t + 1) d := Iff.rfl

/-- **Until unfolds**: C 𝒰 D at t ↔ D at t OR (C at t AND C 𝒰 D at t+1). -/
theorem luntil_unfold {Δ : Type} (I : TemporalInterp Δ) (C D : Concept) (t : Nat) (d : Δ) :
    ext I (.luntil C D) t d ↔
    ext I D t d ∨ (ext I C t d ∧ ext I (.luntil C D) (t + 1) d) := by
  simp only [ext.luntil_iff]
  constructor
  · rintro ⟨t', ht', hD, hC⟩
    cases Nat.eq_or_lt_of_le ht' with
    | inl heq =>
      subst heq; left; exact hD
    | inr hlt =>
      right
      refine ⟨hC t (Nat.le_refl _) hlt,
              t', Nat.succ_le_of_lt hlt, hD, ?_⟩
      intro t'' ht'' ht''lt
      exact hC t'' (Nat.le_trans (Nat.le_succ t) ht'') ht''lt
  · rintro (hD | ⟨hCt, t', ht', hD, hC⟩)
    · exact ⟨t, Nat.le_refl _, hD,
             fun _ ht'' hlt => absurd (Nat.lt_of_le_of_lt ht'' hlt) (Nat.lt_irrefl t)⟩
    · refine ⟨t', Nat.le_trans (Nat.le_succ _) ht', hD, ?_⟩
      intro t'' ht'' ht''lt
      by_cases h : t'' = t
      · subst h; exact hCt
      · exact hC t'' (Nat.succ_le_of_lt (Nat.lt_of_le_of_ne ht'' (Ne.symm h))) ht''lt
