import LTEL.Semantics
import Mathlib.Order.MinMax

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

/-- Concept is in right-hand normal form: a name, ∃r.A, ○A, or □A.
    (The `some` case is NF-EL3 `A ⊑ ∃r.B`; it was missing in an earlier version.) -/
inductive RhsNF : Concept → Prop where
  | name : RhsNF (.name A)
  | some : RhsNF (.name A) → RhsNF (.some r (.name A))
  | next : RhsNF (.name A) → RhsNF (.next (.name A))
  | glob : RhsNF (.name A) → RhsNF (.globally (.name A))

/-- Concept is in left-hand normal form: ⊤, names, meets of names, ∃r.A, ○A, A𝒰B.
    ⊤ is admitted as a left-hand atom (a basic concept à la Baader–Brandt–Lutz);
    it is needed to express left-side ◇ (= ⊤ 𝒰 ·) after normalization. -/
inductive LhsNF : Concept → Prop where
  | top   : LhsNF .top
  | name  : LhsNF (.name A)
  | meet  : LhsNF (.name A) → LhsNF (.name B) → LhsNF (.meet (.name A) (.name B))
  | some  : LhsNF (.name A) → LhsNF (.some r (.name A))
  | next  : LhsNF (.name A) → LhsNF (.next (.name A))
  | luntil : LhsNF (.name A) → LhsNF (.name B) → LhsNF (.luntil (.name A) (.name B))

/-! ## Conservative definition introduction (the normalization engine)

Normalization flattens nested sub-concepts by naming them with **fresh** concept
names.  The key correctness property is *conservativity*: introducing a fresh
name `a` defined to abbreviate a concept `E` is satisfiability-preserving and
reduct-sound.  This is the reusable engine each normalization step invokes.

Note: this is also *why* the L1 statement below is equisatisfiability, **not** a
per-interpretation biconditional `∀ I, models I T ↔ models I T'`.  The latter is
false once fresh names appear: a model of `T` need not interpret the fresh names
as their definitions (e.g. `T = {A ⊑ ∃r.(B⊓C)}` vs. its flattening with a fresh
`X`; take `X := ∅`).  The honest invariant is a conservative extension. -/

/-- `C.mentions a`: concept name `a` occurs in `C`. -/
def Concept.mentions (a : ConceptName) : Concept → Prop
  | .top        => False
  | .name b     => b = a
  | .meet C D   => Concept.mentions a C ∨ Concept.mentions a D
  | .some _ C   => Concept.mentions a C
  | .next C     => Concept.mentions a C
  | .luntil C D => Concept.mentions a C ∨ Concept.mentions a D
  | .globally C => Concept.mentions a C

/-- Reinterpret the fresh name `a` to abbreviate concept `E` (evaluated in the
    original `I`); all other names and the roles are unchanged. -/
def defineInterp {Δ : Type} (I : TemporalInterp Δ) (a : ConceptName) (E : Concept) :
    TemporalInterp Δ where
  snapshot t :=
    { concept := fun B d => if B = a then ext I E t d else (I.snapshot t).concept B d
      role    := (I.snapshot t).role }
  rigid_roles := fun r t₁ t₂ d e => I.rigid_roles r t₁ t₂ d e

/-- **Substitution lemma**: on concepts not mentioning `a`, the redefinition is
    invisible. -/
theorem ext_defineInterp_not_mentions {Δ : Type} (I : TemporalInterp Δ)
    (a : ConceptName) (E : Concept) :
    ∀ (C : Concept), ¬ C.mentions a → ∀ (t : Nat) (d : Δ),
      (ext (defineInterp I a E) C t d ↔ ext I C t d) := by
  intro C
  induction C with
  | top => intro _ t d; exact Iff.rfl
  | name b =>
      intro hb t d
      simp only [Concept.mentions] at hb
      simp only [ext, defineInterp]
      rw [if_neg hb]
  | meet C D ihC ihD =>
      intro h t d
      have hC : ¬ C.mentions a := fun hh => h (Or.inl hh)
      have hD : ¬ D.mentions a := fun hh => h (Or.inr hh)
      simp only [ext]
      exact and_congr (ihC hC t d) (ihD hD t d)
  | some r C ihC =>
      intro h t d
      simp only [ext]
      constructor
      · rintro ⟨e, hr, hCe⟩; exact ⟨e, hr, (ihC h t e).mp hCe⟩
      · rintro ⟨e, hr, hCe⟩; exact ⟨e, hr, (ihC h t e).mpr hCe⟩
  | next C ihC =>
      intro h t d
      simp only [ext]
      exact ihC h (t + 1) d
  | luntil C D ihC ihD =>
      intro h t d
      have hC : ¬ C.mentions a := fun hh => h (Or.inl hh)
      have hD : ¬ D.mentions a := fun hh => h (Or.inr hh)
      simp only [ext]
      constructor
      · rintro ⟨t', ht', hDt, hCt⟩
        exact ⟨t', ht', (ihD hD t' d).mp hDt,
               fun t'' h1 h2 => (ihC hC t'' d).mp (hCt t'' h1 h2)⟩
      · rintro ⟨t', ht', hDt, hCt⟩
        exact ⟨t', ht', (ihD hD t' d).mpr hDt,
               fun t'' h1 h2 => (ihC hC t'' d).mpr (hCt t'' h1 h2)⟩
  | globally C ihC =>
      intro h t d
      simp only [ext]
      constructor
      · intro hall t' ht'; exact (ihC h t' d).mp (hall t' ht')
      · intro hall t' ht'; exact (ihC h t' d).mpr (hall t' ht')

/-- An axiom mentions `a` if `a` occurs in either side of a GCI. -/
def AxMentions (a : ConceptName) : Axiom → Prop
  | .gci C D  => C.mentions a ∨ D.mentions a
  | .ri _ _ _ => False

/-- On axioms not mentioning `a`, the redefinition is invisible. -/
theorem satisfies_defineInterp_not_mentions {Δ : Type} (I : TemporalInterp Δ)
    (a : ConceptName) (E : Concept) (ax : Axiom) (h : ¬ AxMentions a ax) :
    satisfies (defineInterp I a E) ax ↔ satisfies I ax := by
  cases ax with
  | gci C D =>
      have hC : ¬ C.mentions a := fun hh => h (Or.inl hh)
      have hD : ¬ D.mentions a := fun hh => h (Or.inr hh)
      constructor
      · intro hsat t d hCd
        exact (ext_defineInterp_not_mentions I a E D hD t d).mp
                (hsat t d ((ext_defineInterp_not_mentions I a E C hC t d).mpr hCd))
      · intro hsat t d hCd
        exact (ext_defineInterp_not_mentions I a E D hD t d).mpr
                (hsat t d ((ext_defineInterp_not_mentions I a E C hC t d).mp hCd))
  | ri r s u => exact Iff.rfl

/-- In the redefined interpretation, the fresh name `a` is equivalent to `E`
    (provided `a` does not occur in `E`). -/
theorem defineInterp_def_holds {Δ : Type} (I : TemporalInterp Δ)
    (a : ConceptName) (E : Concept) (hE : ¬ E.mentions a) :
    satisfies (defineInterp I a E) (.gci (.name a) E) ∧
    satisfies (defineInterp I a E) (.gci E (.name a)) := by
  have key : ∀ t d, (ext (defineInterp I a E) (.name a) t d ↔ ext (defineInterp I a E) E t d) := by
    intro t d
    rw [ext_defineInterp_not_mentions I a E E hE t d]
    simp only [ext, defineInterp, if_pos]
  exact ⟨fun t d h => (key t d).mp h, fun t d h => (key t d).mpr h⟩

/-- **Conservative definition introduction.**  For a fresh name `a` (not in `T`
    nor in `E`), adding the two axioms `a ⊑ E`, `E ⊑ a` (i.e. `a ≡ E`) is
    satisfiability-preserving.  This is the engine each normalization step runs:
    replace a complex sub-concept by a fresh defined name. -/
theorem definition_introduction_conservative (T : TBox) (a : ConceptName) (E : Concept)
    (hT : ∀ ax ∈ T, ¬ AxMentions a ax) (hE : ¬ E.mentions a) :
    satisfiable T ↔ satisfiable (T ++ [Axiom.gci (.name a) E, Axiom.gci E (.name a)]) := by
  constructor
  · rintro ⟨Δ, I, hI⟩
    refine ⟨Δ, defineInterp I a E, ?_⟩
    intro ax hax
    rcases List.mem_append.mp hax with hin | hin
    · exact (satisfies_defineInterp_not_mentions I a E ax (hT ax hin)).mpr (hI ax hin)
    · obtain ⟨hd1, hd2⟩ := defineInterp_def_holds I a E hE
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
      rcases hin with rfl | rfl
      · exact hd1
      · exact hd2
  · rintro ⟨Δ, I, hI⟩
    exact ⟨Δ, I, fun ax hax => hI ax (List.mem_append.mpr (Or.inl hax))⟩

/-! ## Replacement under a definition (the second half of a normalization step)

    A normalization step (i) introduces a fresh name `a ≡ E` (conservative, above)
    and (ii) *replaces* the complex sub-concept `E` by `a` inside the axioms.  The
    replacement preserves extensions in any interpretation that already satisfies
    `a ≡ E` — proved here.  Engine + replacement = one full normalization step is
    model-preserving. -/

/-- Replace every occurrence of the sub-concept `E` by the concept name `a`. -/
def Concept.replace (C : Concept) (E : Concept) (a : ConceptName) : Concept :=
  if C = E then .name a
  else match C with
    | .top          => .top
    | .name b       => .name b
    | .meet C₁ C₂   => .meet (C₁.replace E a) (C₂.replace E a)
    | .some r C₁    => .some r (C₁.replace E a)
    | .next C₁      => .next (C₁.replace E a)
    | .luntil C₁ C₂ => .luntil (C₁.replace E a) (C₂.replace E a)
    | .globally C₁  => .globally (C₁.replace E a)

/-- **Replacement preserves extension** under a definition `a ≡ E`. -/
theorem ext_replace_of_def {Δ : Type} (I : TemporalInterp Δ) (E : Concept) (a : ConceptName)
    (hdef : ∀ t d, ext I (.name a) t d ↔ ext I E t d) :
    ∀ (C : Concept) (t : Nat) (d : Δ),
      (ext I (C.replace E a) t d ↔ ext I C t d) := by
  intro C
  induction C with
  | top =>
      intro t d
      simp only [Concept.replace]
      by_cases h : (Concept.top : Concept) = E
      · rw [if_pos h, h]; exact hdef t d
      · rw [if_neg h]
  | name b =>
      intro t d
      simp only [Concept.replace]
      by_cases h : (Concept.name b) = E
      · rw [if_pos h, h]; exact hdef t d
      · rw [if_neg h]
  | meet C₁ C₂ ih₁ ih₂ =>
      intro t d
      simp only [Concept.replace]
      by_cases h : (Concept.meet C₁ C₂) = E
      · rw [if_pos h, h]; exact hdef t d
      · rw [if_neg h]
        simp only [ext]
        exact and_congr (ih₁ t d) (ih₂ t d)
  | some r C₁ ih₁ =>
      intro t d
      simp only [Concept.replace]
      by_cases h : (Concept.some r C₁) = E
      · rw [if_pos h, h]; exact hdef t d
      · rw [if_neg h]
        simp only [ext]
        constructor
        · rintro ⟨e, hr, he⟩; exact ⟨e, hr, (ih₁ t e).mp he⟩
        · rintro ⟨e, hr, he⟩; exact ⟨e, hr, (ih₁ t e).mpr he⟩
  | next C₁ ih₁ =>
      intro t d
      simp only [Concept.replace]
      by_cases h : (Concept.next C₁) = E
      · rw [if_pos h, h]; exact hdef t d
      · rw [if_neg h]
        simp only [ext]
        exact ih₁ (t + 1) d
  | luntil C₁ C₂ ih₁ ih₂ =>
      intro t d
      simp only [Concept.replace]
      by_cases h : (Concept.luntil C₁ C₂) = E
      · rw [if_pos h, h]; exact hdef t d
      · rw [if_neg h]
        simp only [ext]
        constructor
        · rintro ⟨t', ht', hD, hC⟩
          exact ⟨t', ht', (ih₂ t' d).mp hD,
                 fun t'' h1 h2 => (ih₁ t'' d).mp (hC t'' h1 h2)⟩
        · rintro ⟨t', ht', hD, hC⟩
          exact ⟨t', ht', (ih₂ t' d).mpr hD,
                 fun t'' h1 h2 => (ih₁ t'' d).mpr (hC t'' h1 h2)⟩
  | globally C₁ ih₁ =>
      intro t d
      simp only [Concept.replace]
      by_cases h : (Concept.globally C₁) = E
      · rw [if_pos h, h]; exact hdef t d
      · rw [if_neg h]
        simp only [ext]
        constructor
        · intro hall t' ht'; exact (ih₁ t' d).mp (hall t' ht')
        · intro hall t' ht'; exact (ih₁ t' d).mpr (hall t' ht')

/-! ## Monotone substitution — the basis of polarity-directional steps

    All LTEL operators are monotone (no negation), so a sub-concept `E` may be
    named by a fresh `a` with a **one-directional** definition, sound when used in
    the matching polarity:
      * a positive (right-hand, super-concept) occurrence needs only `a ⊑ E`
        (e.g. `a ⊑ □B`, which is NF — `□` lives only on the right);
      * a negative (left-hand, sub-concept) occurrence needs only `E ⊑ a`
        (e.g. `B₁ 𝒰 B₂ ⊑ a`, NF — `𝒰` lives only on the left).
    Either inclusion suffices because replacing `E` by `a` is monotone — the two
    lemmas below. -/

/-- If `a ⊆ E`, replacing `E` by `a` can only **shrink** a concept's extension
    (sound for positive/right-hand occurrences). -/
theorem ext_replace_mono_of_sub {Δ : Type} (J : TemporalInterp Δ) (E : Concept) (a : ConceptName)
    (hsub : ∀ t d, ext J (.name a) t d → ext J E t d) :
    ∀ (C : Concept) (t : Nat) (d : Δ), ext J (C.replace E a) t d → ext J C t d := by
  intro C
  induction C with
  | top => intro t d _; exact trivial
  | name b =>
      intro t d h; simp only [Concept.replace] at h
      by_cases hE : (Concept.name b) = E
      · simp only [if_pos hE] at h; rw [hE]; exact hsub t d h
      · simp only [if_neg hE] at h; exact h
  | meet C D ihC ihD =>
      intro t d h; simp only [Concept.replace] at h
      by_cases hE : (Concept.meet C D) = E
      · simp only [if_pos hE] at h; rw [hE]; exact hsub t d h
      · simp only [if_neg hE] at h; simp only [ext] at h ⊢
        exact ⟨ihC t d h.1, ihD t d h.2⟩
  | some r C ihC =>
      intro t d h; simp only [Concept.replace] at h
      by_cases hE : (Concept.some r C) = E
      · simp only [if_pos hE] at h; rw [hE]; exact hsub t d h
      · simp only [if_neg hE] at h; simp only [ext] at h ⊢
        obtain ⟨e, hr, he⟩ := h; exact ⟨e, hr, ihC t e he⟩
  | next C ihC =>
      intro t d h; simp only [Concept.replace] at h
      by_cases hE : (Concept.next C) = E
      · simp only [if_pos hE] at h; rw [hE]; exact hsub t d h
      · simp only [if_neg hE] at h; simp only [ext] at h ⊢; exact ihC (t + 1) d h
  | luntil C D ihC ihD =>
      intro t d h; simp only [Concept.replace] at h
      by_cases hE : (Concept.luntil C D) = E
      · simp only [if_pos hE] at h; rw [hE]; exact hsub t d h
      · simp only [if_neg hE] at h; simp only [ext] at h ⊢
        obtain ⟨t', ht', hD, hC⟩ := h
        exact ⟨t', ht', ihD t' d hD, fun t'' h1 h2 => ihC t'' d (hC t'' h1 h2)⟩
  | globally C ihC =>
      intro t d h; simp only [Concept.replace] at h
      by_cases hE : (Concept.globally C) = E
      · simp only [if_pos hE] at h; rw [hE]; exact hsub t d h
      · simp only [if_neg hE] at h; simp only [ext] at h ⊢
        intro t' ht'; exact ihC t' d (h t' ht')

/-- If `E ⊆ a`, replacing `E` by `a` can only **grow** a concept's extension
    (sound for negative/left-hand occurrences). -/
theorem ext_replace_mono_of_sup {Δ : Type} (J : TemporalInterp Δ) (E : Concept) (a : ConceptName)
    (hsup : ∀ t d, ext J E t d → ext J (.name a) t d) :
    ∀ (C : Concept) (t : Nat) (d : Δ), ext J C t d → ext J (C.replace E a) t d := by
  intro C
  induction C with
  | top =>
      intro t d h; simp only [Concept.replace]
      by_cases hE : (Concept.top : Concept) = E
      · simp only [if_pos hE]; rw [hE] at h; exact hsup t d h
      · simp only [if_neg hE]; exact h
  | name b =>
      intro t d h; simp only [Concept.replace]
      by_cases hE : (Concept.name b) = E
      · simp only [if_pos hE]; rw [hE] at h; exact hsup t d h
      · simp only [if_neg hE]; exact h
  | meet C D ihC ihD =>
      intro t d h; simp only [Concept.replace]
      by_cases hE : (Concept.meet C D) = E
      · simp only [if_pos hE]; rw [hE] at h; exact hsup t d h
      · simp only [if_neg hE]; simp only [ext] at h ⊢
        exact ⟨ihC t d h.1, ihD t d h.2⟩
  | some r C ihC =>
      intro t d h; simp only [Concept.replace]
      by_cases hE : (Concept.some r C) = E
      · simp only [if_pos hE]; rw [hE] at h; exact hsup t d h
      · simp only [if_neg hE]; simp only [ext] at h ⊢
        obtain ⟨e, hr, he⟩ := h; exact ⟨e, hr, ihC t e he⟩
  | next C ihC =>
      intro t d h; simp only [Concept.replace]
      by_cases hE : (Concept.next C) = E
      · simp only [if_pos hE]; rw [hE] at h; exact hsup t d h
      · simp only [if_neg hE]; simp only [ext] at h ⊢; exact ihC (t + 1) d h
  | luntil C D ihC ihD =>
      intro t d h; simp only [Concept.replace]
      by_cases hE : (Concept.luntil C D) = E
      · simp only [if_pos hE]; rw [hE] at h; exact hsup t d h
      · simp only [if_neg hE]; simp only [ext] at h ⊢
        obtain ⟨t', ht', hD, hC⟩ := h
        exact ⟨t', ht', ihD t' d hD, fun t'' h1 h2 => ihC t'' d (hC t'' h1 h2)⟩
  | globally C ihC =>
      intro t d h; simp only [Concept.replace]
      by_cases hE : (Concept.globally C) = E
      · simp only [if_pos hE]; rw [hE] at h; exact hsup t d h
      · simp only [if_neg hE]; simp only [ext] at h ⊢
        intro t' ht'; exact ihC t' d (h t' ht')

/-- Replace `E` by `a` on both sides of an axiom (role inclusions unchanged). -/
def Axiom.replace (E : Concept) (a : ConceptName) : Axiom → Axiom
  | .gci C D  => .gci (C.replace E a) (D.replace E a)
  | .ri r s u => .ri r s u

/-- Under a definition `a ≡ E`, replacement preserves axiom satisfaction. -/
theorem satisfies_replace_of_def {Δ : Type} (J : TemporalInterp Δ) (E : Concept) (a : ConceptName)
    (hdef : ∀ t d, ext J (.name a) t d ↔ ext J E t d) (ax : Axiom) :
    satisfies J (ax.replace E a) ↔ satisfies J ax := by
  cases ax with
  | gci C D =>
      simp only [Axiom.replace]
      constructor
      · intro h t d hC
        exact (ext_replace_of_def J E a hdef D t d).mp
                (h t d ((ext_replace_of_def J E a hdef C t d).mpr hC))
      · intro h t d hC
        exact (ext_replace_of_def J E a hdef D t d).mpr
                (h t d ((ext_replace_of_def J E a hdef C t d).mp hC))
  | ri r s u => exact Iff.rfl

/-! ## One normalization step (fully proved)

    A single step replaces a sub-concept `E` (in every axiom) by a fresh name `a`
    and adds the definition `a ≡ E`.  Combining the conservativity engine with the
    replacement lemma, the step is a conservative extension: equisatisfiable, and
    every model of the result is a model of the input.  The full L1 algorithm
    iterates this step (on a strictly decreasing concept-complexity measure, with
    fresh names) until the NF shapes are reached. -/

/-- **One normalization step is conservative.**  For a fresh name `a` (not in `T`
    nor `E`), replacing `E` by `a` throughout and adding `a ≡ E` preserves
    satisfiability, and every model of the result is a model of `T`. -/
theorem normalization_step_conservative (T : TBox) (a : ConceptName) (E : Concept)
    (hT : ∀ ax ∈ T, ¬ AxMentions a ax) (hE : ¬ E.mentions a) :
    (satisfiable T ↔
      satisfiable (T.map (Axiom.replace E a) ++ [Axiom.gci (.name a) E, Axiom.gci E (.name a)]))
    ∧ (∀ (Δ : Type) (I : TemporalInterp Δ),
        models I (T.map (Axiom.replace E a) ++ [Axiom.gci (.name a) E, Axiom.gci E (.name a)]) →
        models I T) := by
  -- reduct: every model of the step result is a model of T
  have reduct : ∀ (Δ : Type) (I : TemporalInterp Δ),
      models I (T.map (Axiom.replace E a) ++ [Axiom.gci (.name a) E, Axiom.gci E (.name a)]) →
      models I T := by
    intro Δ I hI' ax hax
    have hd1 : satisfies I (Axiom.gci (.name a) E) :=
      hI' _ (List.mem_append.mpr (Or.inr (by simp)))
    have hd2 : satisfies I (Axiom.gci E (.name a)) :=
      hI' _ (List.mem_append.mpr (Or.inr (by simp)))
    have hdef : ∀ t d, ext I (.name a) t d ↔ ext I E t d :=
      fun t d => ⟨fun h => hd1 t d h, fun h => hd2 t d h⟩
    have hrep : satisfies I (ax.replace E a) :=
      hI' _ (List.mem_append.mpr (Or.inl (List.mem_map_of_mem hax)))
    exact (satisfies_replace_of_def I E a hdef ax).mp hrep
  refine ⟨⟨?_, ?_⟩, reduct⟩
  · -- (→) satisfiable T → satisfiable (step)
    rintro ⟨Δ, I, hI⟩
    refine ⟨Δ, defineInterp I a E, ?_⟩
    obtain ⟨hd1, hd2⟩ := defineInterp_def_holds I a E hE
    have hdef : ∀ t d, ext (defineInterp I a E) (.name a) t d ↔ ext (defineInterp I a E) E t d :=
      fun t d => ⟨fun h => hd1 t d h, fun h => hd2 t d h⟩
    intro ax hax
    rcases List.mem_append.mp hax with hin | hin
    · obtain ⟨ax₀, hax₀, rfl⟩ := List.mem_map.mp hin
      rw [satisfies_replace_of_def (defineInterp I a E) E a hdef ax₀]
      exact (satisfies_defineInterp_not_mentions I a E ax₀ (hT ax₀ hax₀)).mpr (hI ax₀ hax₀)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
      rcases hin with rfl | rfl
      · exact hd1
      · exact hd2
  · -- (←) satisfiable (step) → satisfiable T, via reduct
    rintro ⟨Δ, I, hI'⟩
    exact ⟨Δ, I, reduct Δ I hI'⟩

/-! ## Fresh-name supply (fully proved)

    Each step needs a name not occurring in the current TBox.  `freshName T` is
    one more than the largest name in `T`, and is provably unmentioned. -/

/-- The largest concept name occurring in `C` (0 if none). -/
def Concept.maxName : Concept → Nat
  | .top        => 0
  | .name b     => b
  | .meet C D   => max C.maxName D.maxName
  | .some _ C   => C.maxName
  | .next C     => C.maxName
  | .luntil C D => max C.maxName D.maxName
  | .globally C => C.maxName

theorem mentions_le_maxName (a : ConceptName) :
    ∀ (C : Concept), C.mentions a → a ≤ C.maxName := by
  intro C
  induction C with
  | top => intro h; exact absurd h (by simp [Concept.mentions])
  | name b => intro h; simp only [Concept.mentions] at h; subst h; simp [Concept.maxName]
  | meet C D ihC ihD =>
      intro h; simp only [Concept.mentions] at h; simp only [Concept.maxName]
      rcases h with h | h
      · exact le_trans (ihC h) (le_max_left _ _)
      · exact le_trans (ihD h) (le_max_right _ _)
  | some r C ihC => intro h; simp only [Concept.mentions] at h; exact ihC h
  | next C ihC => intro h; simp only [Concept.mentions] at h; exact ihC h
  | luntil C D ihC ihD =>
      intro h; simp only [Concept.mentions] at h; simp only [Concept.maxName]
      rcases h with h | h
      · exact le_trans (ihC h) (le_max_left _ _)
      · exact le_trans (ihD h) (le_max_right _ _)
  | globally C ihC => intro h; simp only [Concept.mentions] at h; exact ihC h

/-- The largest name occurring in an axiom. -/
def Axiom.maxName : Axiom → Nat
  | .gci C D  => max C.maxName D.maxName
  | .ri _ _ _ => 0

theorem axMentions_le_maxName (a : ConceptName) (ax : Axiom) :
    AxMentions a ax → a ≤ ax.maxName := by
  cases ax with
  | gci C D =>
      intro h
      simp only [AxMentions] at h
      simp only [Axiom.maxName]
      rcases h with h | h
      · exact le_trans (mentions_le_maxName a C h) (le_max_left _ _)
      · exact le_trans (mentions_le_maxName a D h) (le_max_right _ _)
  | ri r s u => intro h; exact absurd h (by simp [AxMentions])

/-- The largest name occurring in a TBox. -/
def TBox.maxName (T : TBox) : Nat := T.foldr (fun ax n => max ax.maxName n) 0

theorem axMaxName_le_tboxMaxName (ax : Axiom) (T : TBox) :
    ax ∈ T → ax.maxName ≤ T.maxName := by
  induction T with
  | nil => intro h; exact absurd h (by simp)
  | cons b t ih =>
      intro h
      simp only [TBox.maxName, List.foldr_cons]
      rcases List.mem_cons.mp h with h | h
      · subst h; exact le_max_left _ _
      · exact le_trans (ih h) (le_max_right _ _)

/-- A name guaranteed not to occur in `T`. -/
def freshName (T : TBox) : ConceptName := T.maxName + 1

/-- `freshName T` is unmentioned by every axiom of `T`. -/
theorem freshName_not_mentions (T : TBox) :
    ∀ ax ∈ T, ¬ AxMentions (freshName T) ax := by
  intro ax hax hm
  have h1 : freshName T ≤ ax.maxName := axMentions_le_maxName _ ax hm
  have h2 : ax.maxName ≤ T.maxName := axMaxName_le_tboxMaxName ax T hax
  have : T.maxName + 1 ≤ T.maxName := le_trans h1 h2
  exact Nat.not_succ_le_self _ this

/-! ## Composing steps: the iteration glue (fully proved)

    The well-founded iteration produces a chain `T = T₀ ⤳ T₁ ⤳ … ⤳ Tₙ` of
    conservative steps ending in normal form.  The *composition* of that chain is
    captured here: `Conservative` is reflexive and transitive, and each step is
    `Conservative`.  So once the recursion produces the chain, its overall
    correctness is immediate.  What remains for full L1 is the recursion that
    *builds* the chain (a strictly decreasing complexity measure + fresh names);
    see the L1 note. -/

/-- A conservative extension: equisatisfiable, and every model of `T'` is a model
    of `T`.  The invariant each step maintains and the iteration composes. -/
def Conservative (T T' : TBox) : Prop :=
  (satisfiable T ↔ satisfiable T') ∧
  (∀ (Δ : Type) (I : TemporalInterp Δ), models I T' → models I T)

theorem Conservative.refl (T : TBox) : Conservative T T :=
  ⟨Iff.rfl, fun _ _ h => h⟩

theorem Conservative.trans {T₁ T₂ T₃ : TBox}
    (h₁ : Conservative T₁ T₂) (h₂ : Conservative T₂ T₃) : Conservative T₁ T₃ :=
  ⟨h₁.1.trans h₂.1, fun Δ I h => h₁.2 Δ I (h₂.2 Δ I h)⟩

/-- Each normalization step is conservative (repackages
    `normalization_step_conservative`). -/
theorem Conservative.step (T : TBox) (a : ConceptName) (E : Concept)
    (hT : ∀ ax ∈ T, ¬ AxMentions a ax) (hE : ¬ E.mentions a) :
    Conservative T
      (T.map (Axiom.replace E a) ++ [Axiom.gci (.name a) E, Axiom.gci E (.name a)]) :=
  ⟨(normalization_step_conservative T a E hT hE).1,
   (normalization_step_conservative T a E hT hE).2⟩

/-- **Positive (right-hand) directional step.**  Name a sub-concept `E` of the
    super-concept `D` by a fresh `a`, adding only the NF-friendly axiom `a ⊑ E`.
    Conservative — the reduct uses monotonicity (`ext_replace_mono_of_sub`).
    For `□B` on the right this gives `a ⊑ □B` (NF-T3); no `□B ⊑ a` needed. -/
theorem Conservative.directional_rhs (C D E : Concept) (a : ConceptName)
    (hfresh : ¬ AxMentions a (Axiom.gci C D)) (hE : ¬ E.mentions a) :
    Conservative [Axiom.gci C D]
      [Axiom.gci C (D.replace E a), Axiom.gci (.name a) E] := by
  have reduct : ∀ (Δ : Type) (I : TemporalInterp Δ),
      models I [Axiom.gci C (D.replace E a), Axiom.gci (.name a) E] →
      models I [Axiom.gci C D] := by
    intro Δ I hI ax hmem
    simp only [List.mem_singleton] at hmem; subst hmem
    have h1 := hI (Axiom.gci C (D.replace E a)) (by simp)
    have h2 := hI (Axiom.gci (.name a) E) (by simp)
    intro t d hCd
    exact ext_replace_mono_of_sub I E a (fun t d h => h2 t d h) D t d (h1 t d hCd)
  refine ⟨⟨?_, fun h => h.elim fun Δ h => h.elim fun I hI => ⟨Δ, I, reduct Δ I hI⟩⟩, reduct⟩
  rintro ⟨Δ, I, hI⟩
  have hax := hI (Axiom.gci C D) (by simp)
  refine ⟨Δ, defineInterp I a E, ?_⟩
  obtain ⟨hd1, hd2⟩ := defineInterp_def_holds I a E hE
  have hdef : ∀ t d, ext (defineInterp I a E) (.name a) t d ↔ ext (defineInterp I a E) E t d :=
    fun t d => ⟨fun h => hd1 t d h, fun h => hd2 t d h⟩
  intro ax hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  · intro t d hCd
    have hCD := (satisfies_defineInterp_not_mentions I a E (Axiom.gci C D) hfresh).mpr hax
    exact (ext_replace_of_def (defineInterp I a E) E a hdef D t d).mpr (hCD t d hCd)
  · exact hd1

/-- **Negative (left-hand) directional step.**  Name a sub-concept `E` of the
    sub-concept `C` by a fresh `a`, adding only the NF-friendly axiom `E ⊑ a`.
    Conservative — the reduct uses monotonicity (`ext_replace_mono_of_sup`).
    For `B₁ 𝒰 B₂` on the left this gives `B₁ 𝒰 B₂ ⊑ a` (NF-T4); no `a ⊑ …` needed. -/
theorem Conservative.directional_lhs (C D E : Concept) (a : ConceptName)
    (hfresh : ¬ AxMentions a (Axiom.gci C D)) (hE : ¬ E.mentions a) :
    Conservative [Axiom.gci C D]
      [Axiom.gci (C.replace E a) D, Axiom.gci E (.name a)] := by
  have reduct : ∀ (Δ : Type) (I : TemporalInterp Δ),
      models I [Axiom.gci (C.replace E a) D, Axiom.gci E (.name a)] →
      models I [Axiom.gci C D] := by
    intro Δ I hI ax hmem
    simp only [List.mem_singleton] at hmem; subst hmem
    have h1 := hI (Axiom.gci (C.replace E a) D) (by simp)
    have h2 := hI (Axiom.gci E (.name a)) (by simp)
    intro t d hCd
    exact h1 t d (ext_replace_mono_of_sup I E a (fun t d h => h2 t d h) C t d hCd)
  refine ⟨⟨?_, fun h => h.elim fun Δ h => h.elim fun I hI => ⟨Δ, I, reduct Δ I hI⟩⟩, reduct⟩
  rintro ⟨Δ, I, hI⟩
  have hax := hI (Axiom.gci C D) (by simp)
  refine ⟨Δ, defineInterp I a E, ?_⟩
  obtain ⟨hd1, hd2⟩ := defineInterp_def_holds I a E hE
  have hdef : ∀ t d, ext (defineInterp I a E) (.name a) t d ↔ ext (defineInterp I a E) E t d :=
    fun t d => ⟨fun h => hd1 t d h, fun h => hd2 t d h⟩
  intro ax hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  · intro t d hCd
    have hCD := (satisfies_defineInterp_not_mentions I a E (Axiom.gci C D) hfresh).mpr hax
    exact hCD t d ((ext_replace_of_def (defineInterp I a E) E a hdef C t d).mp hCd)
  · exact hd2

/-- **Meet-split on the right.**  `C ⊑ D ⊓ E` is equivalent to `{C ⊑ D, C ⊑ E}`.
    This turns the one non-NF output of a meet step (`a ⊑ B₁ ⊓ B₂`, a meet on the
    right) into two NF-EL1 axioms — the last shape needed for NF-producing steps. -/
theorem Conservative.split_meet_rhs (C D E : Concept) :
    Conservative [Axiom.gci C (Concept.meet D E)] [Axiom.gci C D, Axiom.gci C E] := by
  have reduct : ∀ (Δ : Type) (I : TemporalInterp Δ),
      models I [Axiom.gci C D, Axiom.gci C E] → models I [Axiom.gci C (Concept.meet D E)] := by
    intro Δ I hI ax hmem
    simp only [List.mem_singleton] at hmem; subst hmem
    intro t d hC
    exact ⟨(hI (Axiom.gci C D) (by simp)) t d hC, (hI (Axiom.gci C E) (by simp)) t d hC⟩
  refine ⟨⟨?_, fun h => h.elim fun Δ h => h.elim fun I hI => ⟨Δ, I, reduct Δ I hI⟩⟩, reduct⟩
  rintro ⟨Δ, I, hI⟩
  have hax := hI (Axiom.gci C (Concept.meet D E)) (by simp)
  refine ⟨Δ, I, ?_⟩
  intro ax hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  · intro t d hC; exact (hax t d hC).1
  · intro t d hC; exact (hax t d hC).2

/-! ## Termination measure (partial)

    The iteration's measure is `cpx`: the number of **complex proper
    sub-concepts** (non-atomic occurrences nested below an operator).  `cpx = 0`
    exactly on the NF-able shapes, and a step on an innermost complex `E` should
    strictly decrease it.  The foundational fact is monotonicity — replacing a
    sub-concept by a name never increases `cpx` — proved here. -/

/-- A concept is complex if it is not a name or `⊤`. -/
def Concept.isComplex : Concept → Bool
  | .name _ => false
  | .top    => false
  | _       => true

/-- Number of complex proper sub-concept occurrences (the termination measure). -/
def Concept.cpx : Concept → Nat
  | .top        => 0
  | .name _     => 0
  | .meet C D   => (if C.isComplex then 1 else 0) + C.cpx + ((if D.isComplex then 1 else 0) + D.cpx)
  | .some _ C   => (if C.isComplex then 1 else 0) + C.cpx
  | .next C     => (if C.isComplex then 1 else 0) + C.cpx
  | .luntil C D => (if C.isComplex then 1 else 0) + C.cpx + ((if D.isComplex then 1 else 0) + D.cpx)
  | .globally C => (if C.isComplex then 1 else 0) + C.cpx

/-- Replacing a sub-concept by a name does not increase the "is-complex" bit. -/
theorem complexBit_replace_le (E : Concept) (a : ConceptName) (C : Concept) :
    (if (C.replace E a).isComplex then (1 : Nat) else 0) ≤ (if C.isComplex then 1 else 0) := by
  cases C with
  | name b =>
      simp only [Concept.replace]; by_cases h : Concept.name b = E
      · simp only [if_pos h]; simp [Concept.isComplex]
      · simp only [if_neg h]; simp [Concept.isComplex]
  | top =>
      simp only [Concept.replace]; by_cases h : (Concept.top : Concept) = E
      · simp only [if_pos h]; simp [Concept.isComplex]
      · simp only [if_neg h]; simp [Concept.isComplex]
  | meet C1 C2 =>
      simp only [Concept.replace]; by_cases h : Concept.meet C1 C2 = E
      · simp only [if_pos h]; simp [Concept.isComplex]
      · simp only [if_neg h]; simp [Concept.isComplex]
  | some r C1 =>
      simp only [Concept.replace]; by_cases h : Concept.some r C1 = E
      · simp only [if_pos h]; simp [Concept.isComplex]
      · simp only [if_neg h]; simp [Concept.isComplex]
  | next C1 =>
      simp only [Concept.replace]; by_cases h : Concept.next C1 = E
      · simp only [if_pos h]; simp [Concept.isComplex]
      · simp only [if_neg h]; simp [Concept.isComplex]
  | luntil C1 C2 =>
      simp only [Concept.replace]; by_cases h : Concept.luntil C1 C2 = E
      · simp only [if_pos h]; simp [Concept.isComplex]
      · simp only [if_neg h]; simp [Concept.isComplex]
  | globally C1 =>
      simp only [Concept.replace]; by_cases h : Concept.globally C1 = E
      · simp only [if_pos h]; simp [Concept.isComplex]
      · simp only [if_neg h]; simp [Concept.isComplex]

/-- **Monotonicity of the measure**: replacing a sub-concept `E` by a name `a`
    never increases `cpx`.  (The strict-decrease version, needed for termination,
    additionally requires that `E` actually occurs as a complex proper
    sub-concept — that and the picker are the remaining work.) -/
theorem cpx_replace_le (E : Concept) (a : ConceptName) :
    ∀ (C : Concept), (C.replace E a).cpx ≤ C.cpx := by
  intro C
  induction C with
  | top =>
      simp only [Concept.replace]; by_cases h : (Concept.top : Concept) = E
      · simp only [if_pos h]; simp [Concept.cpx]
      · simp only [if_neg h]; simp [Concept.cpx]
  | name b =>
      simp only [Concept.replace]; by_cases h : (Concept.name b) = E
      · simp only [if_pos h]; simp [Concept.cpx]
      · simp only [if_neg h]; simp [Concept.cpx]
  | meet C D ihC ihD =>
      simp only [Concept.replace]; by_cases h : (Concept.meet C D) = E
      · simp only [if_pos h]; simp [Concept.cpx]
      · simp only [if_neg h]; simp only [Concept.cpx]
        have hC := complexBit_replace_le E a C
        have hD := complexBit_replace_le E a D
        omega
  | some r C ihC =>
      simp only [Concept.replace]; by_cases h : (Concept.some r C) = E
      · simp only [if_pos h]; simp [Concept.cpx]
      · simp only [if_neg h]; simp only [Concept.cpx]
        have hC := complexBit_replace_le E a C
        omega
  | next C ihC =>
      simp only [Concept.replace]; by_cases h : (Concept.next C) = E
      · simp only [if_pos h]; simp [Concept.cpx]
      · simp only [if_neg h]; simp only [Concept.cpx]
        have hC := complexBit_replace_le E a C
        omega
  | luntil C D ihC ihD =>
      simp only [Concept.replace]; by_cases h : (Concept.luntil C D) = E
      · simp only [if_pos h]; simp [Concept.cpx]
      · simp only [if_neg h]; simp only [Concept.cpx]
        have hC := complexBit_replace_le E a C
        have hD := complexBit_replace_le E a D
        omega
  | globally C ihC =>
      simp only [Concept.replace]; by_cases h : (Concept.globally C) = E
      · simp only [if_pos h]; simp [Concept.cpx]
      · simp only [if_neg h]; simp only [Concept.cpx]
        have hC := complexBit_replace_le E a C
        omega

/-! ## L1: Normal form — proved in `LTEL.ELNormalForm`

The normal-form lemma is **proved** — for the polarity-respecting fragment,
which is the only fragment where it is true (right-side ◇/𝒰 have no sound NF;
see Q3) — in `LTEL.ELNormalForm`:

  * `l1_ltel_normal_form` — full polarity fragment (left sides over
    {⊤, names, ⊓, ∃r, ○, 𝒰} hence also ◇ = ⊤𝒰·; right sides over
    {names, ⊓, ∃r, ○, □}), via the executable normalizer `normTBoxEL`, as a
    conservative extension (equisatisfiable + reduct-sound).  No `sorry`.
  * `l1_el_normal_form` — the static-EL instance, derived from it.

An earlier unconditional statement (`l1_normal_form_exists`, quantifying over
arbitrary TBoxes) was removed: without the polarity precondition the lemma is
not provable (e.g. `A ⊑ ◇B` has no faithful NF form), and keeping a
false-as-stated `sorry` would be a hazard.  The step toolkit in this module
(`normalization_step_conservative`, the directional steps, `split_meet_rhs`,
the `cpx` measure) documents the alternative iterate-a-step route; the driver
actually used in `ELNormalForm` is structural recursion via polarity-aware
flatteners, which needs no termination measure. -/

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
