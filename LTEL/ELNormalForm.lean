import LTEL.NormalForm

/-!
# L1 for the EL fragment: complete, machine-checked normalization

End-to-end normal-form theorem for the **static EL fragment** (concepts built
from names, ⊓, ∃r — no temporal operators, ⊤ excluded from inputs for
simplicity).  Unlike the general L1 driver, this closes fully:

  * `flattenL` / `flattenR` — polarity-aware structural-recursion flatteners
    producing NF axioms and an atom name, threading a fresh-name counter.
    Structural recursion on the concept replaces the well-founded TBox measure.
  * Soundness: models of the produced axioms satisfy the represented inclusion.
  * Completeness: any model extends (by interpreting fresh names as the exact
    extensions of the sub-concepts they name, via iterated `defineInterp`) to a
    model of the produced axioms.
  * `l1_el_normal_form` — the EL instance of L1, with the conservative-extension
    guarantee, **no sorry**.

⊤ is excluded because `LhsNF`/`RhsNF` have no ⊤ atom; treating ⊤ as a basic
concept (à la Baader–Brandt–Lutz) would extend both predicates and the driver
mechanically.  The temporal cases of the flatteners return junk and are never
reached under the `ELConcept` hypothesis.
-/

variable {Δ : Type}

/-! ## The EL fragment -/

/-- Concepts of the static EL fragment: names, ⊓, ∃r (no ⊤, no temporal). -/
inductive ELConcept : Concept → Prop where
  | name : ELConcept (.name A)
  | meet : ELConcept C → ELConcept D → ELConcept (.meet C D)
  | some : ELConcept C → ELConcept (.some r C)

/-- An axiom of the EL fragment. -/
def ELAxiom : Axiom → Prop
  | .gci C D  => ELConcept C ∧ ELConcept D
  | .ri _ _ _ => True

/-- A TBox of the EL fragment. -/
def ELTBox (T : TBox) : Prop := ∀ ax ∈ T, ELAxiom ax

/-! ## The polarity fragment (full LTEL L1)

    Left (negative) sides admit {⊤, names, ⊓, ∃r, ○, 𝒰} — hence also ◇ = ⊤𝒰·;
    right (positive) sides admit {⊤, names, ⊓, ∃r, ○, □}.  Right-side 𝒰/◇ are
    excluded: provably unsound to box (Q3).  Left-side □ is excluded: it has no
    NF shape.  All admitted operators are monotone, so one-sided naming is sound
    in the matching polarity. -/

/-- Concepts admissible on the LEFT (negative) side. -/
inductive NegConcept : Concept → Prop where
  | top  : NegConcept .top
  | name : NegConcept (.name A)
  | meet : NegConcept C → NegConcept D → NegConcept (.meet C D)
  | some : NegConcept C → NegConcept (.some r C)
  | next : NegConcept C → NegConcept (.next C)
  | luntil : NegConcept C → NegConcept D → NegConcept (.luntil C D)

/-- Concepts admissible on the RIGHT (positive) side. -/
inductive PosConcept : Concept → Prop where
  | top  : PosConcept .top
  | name : PosConcept (.name A)
  | meet : PosConcept C → PosConcept D → PosConcept (.meet C D)
  | some : PosConcept C → PosConcept (.some r C)
  | next : PosConcept C → PosConcept (.next C)
  | globally : PosConcept C → PosConcept (.globally C)

/-- An axiom of the polarity fragment. -/
def PolarityAxiom : Axiom → Prop
  | .gci C D  => NegConcept C ∧ PosConcept D
  | .ri _ _ _ => True

/-- A TBox of the polarity fragment. -/
def PolarityTBox (T : TBox) : Prop := ∀ ax ∈ T, PolarityAxiom ax

/-- EL concepts sit inside both polarities. -/
theorem ELConcept.neg {C : Concept} (h : ELConcept C) : NegConcept C := by
  induction h with
  | name => exact NegConcept.name
  | meet _ _ ihC ihD => exact NegConcept.meet ihC ihD
  | some _ ihC => exact NegConcept.some ihC

theorem ELConcept.pos {C : Concept} (h : ELConcept C) : PosConcept C := by
  induction h with
  | name => exact PosConcept.name
  | meet _ _ ihC ihD => exact PosConcept.meet ihC ihD
  | some _ ihC => exact PosConcept.some ihC

theorem ELTBox.polarity {T : TBox} (h : ELTBox T) : PolarityTBox T := by
  intro ax hax
  have hEL := h ax hax
  cases ax with
  | gci C D => exact ⟨hEL.1.neg, hEL.2.pos⟩
  | ri r s u => trivial

/-! ## Name bounds -/

/-- All names mentioned in `C` are `< n`.
    NB: the binder is `Nat`, not the `ConceptName` abbrev — `omega` in this
    toolchain only recognises syntactically `Nat`-typed fvars. -/
def Concept.namesBelow (C : Concept) (n : Nat) : Prop :=
  ∀ b : Nat, C.mentions b → b < n

def Axiom.namesBelow : Axiom → Nat → Prop
  | .gci C D, n  => C.namesBelow n ∧ D.namesBelow n
  | .ri _ _ _, _ => True

def TBox.namesBelow (T : TBox) (n : Nat) : Prop :=
  ∀ ax ∈ T, ax.namesBelow n

theorem Concept.namesBelow.mono {C : Concept} {n m : Nat}
    (h : C.namesBelow n) (hnm : n ≤ m) : C.namesBelow m :=
  fun b hb => Nat.lt_of_lt_of_le (h b hb) hnm

theorem Axiom.namesBelow.mono {ax : Axiom} {n m : Nat}
    (h : ax.namesBelow n) (hnm : n ≤ m) : ax.namesBelow m := by
  cases ax with
  | gci C D => exact ⟨h.1.mono hnm, h.2.mono hnm⟩
  | ri r s u => trivial

theorem TBox.namesBelow.mono {T : TBox} {n m : Nat}
    (h : T.namesBelow n) (hnm : n ≤ m) : T.namesBelow m :=
  fun ax hax => (h ax hax).mono hnm

theorem TBox.namesBelow.append {X Y : TBox} {n : Nat}
    (hX : X.namesBelow n) (hY : Y.namesBelow n) : (X ++ Y).namesBelow n := by
  intro ax hax
  rcases List.mem_append.mp hax with h | h
  · exact hX ax h
  · exact hY ax h

theorem not_mentions_of_namesBelow {C : Concept} {n a : Nat}
    (h : C.namesBelow n) (hna : n ≤ a) : ¬ C.mentions a :=
  fun hm => absurd (h a hm) (Nat.not_lt.mpr hna)

/-- Every TBox is name-bounded by its fresh name. -/
theorem namesBelow_freshName (T : TBox) : T.namesBelow (freshName T) := by
  intro ax hax
  cases ax with
  | gci C D =>
      have h3 := axMaxName_le_tboxMaxName _ T hax
      constructor
      · intro b hb
        have h1 := mentions_le_maxName b C hb
        have h2 : C.maxName ≤ (Axiom.gci C D).maxName := le_max_left _ _
        have h4 : b ≤ T.maxName := Nat.le_trans h1 (Nat.le_trans h2 h3)
        simp only [freshName]; omega
      · intro b hb
        have h1 := mentions_le_maxName b D hb
        have h2 : D.maxName ≤ (Axiom.gci C D).maxName := le_max_right _ _
        have h4 : b ≤ T.maxName := Nat.le_trans h1 (Nat.le_trans h2 h3)
        simp only [freshName]; omega
  | ri r s u => trivial

/-! ## Agreement below a name bound -/

/-- `I'` agrees with `I` on all concept names `< n` and on all roles. -/
structure AgreeBelow (I I' : TemporalInterp Δ) (n : Nat) : Prop where
  concept : ∀ b, b < n → ∀ t d, (I'.snapshot t).concept b d ↔ (I.snapshot t).concept b d
  role    : ∀ r t d e, (I'.snapshot t).role r d e ↔ (I.snapshot t).role r d e

theorem AgreeBelow.rfl (I : TemporalInterp Δ) (n : Nat) : AgreeBelow I I n :=
  ⟨fun _ _ _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl⟩

/-- Chain two agreements (the second extends further up). -/
theorem AgreeBelow.chain {I₁ I₂ I₃ : TemporalInterp Δ} {n m : Nat}
    (h₁ : AgreeBelow I₁ I₂ n) (h₂ : AgreeBelow I₂ I₃ m) (hnm : n ≤ m) :
    AgreeBelow I₁ I₃ n :=
  ⟨fun b hb t d => (h₂.concept b (Nat.lt_of_lt_of_le hb hnm) t d).trans (h₁.concept b hb t d),
   fun r t d e => (h₂.role r t d e).trans (h₁.role r t d e)⟩

/-- `defineInterp` only touches the name `a`, so it agrees below any `n ≤ a`. -/
theorem agree_defineInterp (I : TemporalInterp Δ) (a : Nat) (E : Concept)
    {n : Nat} (hna : n ≤ a) :
    AgreeBelow I (defineInterp I a E) n := by
  refine ⟨fun b hb t d => ?_, fun r t d e => Iff.rfl⟩
  simp only [defineInterp]
  rw [if_neg (by omega : ¬ b = a)]

/-- Extension transfers along agreement, for name-bounded concepts. -/
theorem ext_agree {I I' : TemporalInterp Δ} {n : Nat} (hag : AgreeBelow I I' n) :
    ∀ (C : Concept), C.namesBelow n → ∀ (t : Nat) (d : Δ),
      (ext I' C t d ↔ ext I C t d) := by
  intro C
  induction C with
  | top => intro _ t d; exact Iff.rfl
  | name b => intro h t d; exact hag.concept b (h b rfl) t d
  | meet C D ihC ihD =>
      intro h t d
      have hC : C.namesBelow n := fun b hb => h b (Or.inl hb)
      have hD : D.namesBelow n := fun b hb => h b (Or.inr hb)
      simp only [ext]
      exact and_congr (ihC hC t d) (ihD hD t d)
  | some r C ihC =>
      intro h t d
      simp only [ext]
      constructor
      · rintro ⟨e, hr, he⟩
        exact ⟨e, (hag.role r 0 d e).mp hr, (ihC h t e).mp he⟩
      · rintro ⟨e, hr, he⟩
        exact ⟨e, (hag.role r 0 d e).mpr hr, (ihC h t e).mpr he⟩
  | next C ihC =>
      intro h t d
      simp only [ext]
      exact ihC h (t + 1) d
  | luntil C D ihC ihD =>
      intro h t d
      have hC : C.namesBelow n := fun b hb => h b (Or.inl hb)
      have hD : D.namesBelow n := fun b hb => h b (Or.inr hb)
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

/-- Satisfaction transfers along agreement, for name-bounded axioms. -/
theorem satisfies_agree {I I' : TemporalInterp Δ} {n : Nat} (hag : AgreeBelow I I' n)
    {ax : Axiom} (h : ax.namesBelow n) :
    satisfies I' ax ↔ satisfies I ax := by
  cases ax with
  | gci C D =>
      constructor
      · intro hs t d hC
        exact (ext_agree hag D h.2 t d).mp (hs t d ((ext_agree hag C h.1 t d).mpr hC))
      · intro hs t d hC
        exact (ext_agree hag D h.2 t d).mpr (hs t d ((ext_agree hag C h.1 t d).mp hC))
  | ri r s u =>
      constructor
      · intro hs d e f hr hsf
        exact (hag.role u 0 d f).mp
                (hs d e f ((hag.role r 0 d e).mpr hr) ((hag.role s 0 e f).mpr hsf))
      · intro hs d e f hr hsf
        exact (hag.role u 0 d f).mpr
                (hs d e f ((hag.role r 0 d e).mp hr) ((hag.role s 0 e f).mp hsf))

/-- Model-hood transfers along agreement, for name-bounded TBoxes. -/
theorem models_agree {I I' : TemporalInterp Δ} {n : Nat} (hag : AgreeBelow I I' n)
    {T : TBox} (h : T.namesBelow n) :
    models I' T ↔ models I T :=
  ⟨fun hm ax hax => (satisfies_agree hag (h ax hax)).mp (hm ax hax),
   fun hm ax hax => (satisfies_agree hag (h ax hax)).mpr (hm ax hax)⟩

/-- Models decompose over append. -/
theorem models_append {I : TemporalInterp Δ} {X Y : TBox} :
    models I (X ++ Y) ↔ models I X ∧ models I Y := by
  constructor
  · intro h
    exact ⟨fun ax hax => h ax (List.mem_append.mpr (Or.inl hax)),
           fun ax hax => h ax (List.mem_append.mpr (Or.inr hax))⟩
  · rintro ⟨h1, h2⟩ ax hax
    rcases List.mem_append.mp hax with h | h
    · exact h1 ax h
    · exact h2 ax h

/-! ## The polarity-aware flatteners

    `flattenL C n` (negative/left occurrences) returns an atom `a`, NF axioms
    entailing `C ⊑ a`, and the next fresh counter.  `flattenR` is dual
    (axioms entail `a ⊑ C`).  Structural recursion on the concept — no
    well-founded TBox measure needed.  Non-EL constructors return junk and are
    unreachable under `ELConcept`. -/

/-- Result of flattening: representative atom, emitted NF axioms, next counter.
    `atom : Nat` (= `ConceptName`) so `omega` can reason about it. -/
structure FlatRes where
  atom : Nat
  axs  : TBox
  next : Nat

/-- Flatten a **left-hand** (negative) occurrence: axioms entail `C ⊑ atom`. -/
def flattenL : Concept → Nat → FlatRes
  | .name b, n => ⟨b, [], n⟩
  | .meet C D, n =>
      let f := flattenL C n
      let g := flattenL D f.next
      ⟨g.next,
       f.axs ++ g.axs ++ [.gci (.meet (.name f.atom) (.name g.atom)) (.name g.next)],
       g.next + 1⟩
  | .some r C, n =>
      let f := flattenL C n
      ⟨f.next, f.axs ++ [.gci (.some r (.name f.atom)) (.name f.next)], f.next + 1⟩
  | .top, n => ⟨n, [.gci .top (.name n)], n + 1⟩
  | .next C, n =>
      let f := flattenL C n
      ⟨f.next, f.axs ++ [.gci (.next (.name f.atom)) (.name f.next)], f.next + 1⟩
  | .luntil C D, n =>
      let f := flattenL C n
      let g := flattenL D f.next
      ⟨g.next,
       f.axs ++ g.axs ++ [.gci (.luntil (.name f.atom) (.name g.atom)) (.name g.next)],
       g.next + 1⟩
  | .globally _, n => ⟨n, [], n + 1⟩   -- left-□ not in the polarity fragment: junk

/-- Flatten a **right-hand** (positive) occurrence: axioms entail `atom ⊑ C`. -/
def flattenR : Concept → Nat → FlatRes
  | .name b, n => ⟨b, [], n⟩
  | .meet C D, n =>
      let f := flattenR C n
      let g := flattenR D f.next
      ⟨g.next,
       f.axs ++ g.axs ++
         [.gci (.name g.next) (.name f.atom), .gci (.name g.next) (.name g.atom)],
       g.next + 1⟩
  | .some r C, n =>
      let f := flattenR C n
      ⟨f.next, f.axs ++ [.gci (.name f.next) (.some r (.name f.atom))], f.next + 1⟩
  | .top, n => ⟨n, [], n + 1⟩           -- atom ⊑ ⊤ holds vacuously: no axiom needed
  | .next C, n =>
      let f := flattenR C n
      ⟨f.next, f.axs ++ [.gci (.name f.next) (.next (.name f.atom))], f.next + 1⟩
  | .luntil _ _, n => ⟨n, [], n + 1⟩    -- right-𝒰/◇ unsound (Q3): junk
  | .globally C, n =>
      let f := flattenR C n
      ⟨f.next, f.axs ++ [.gci (.name f.next) (.globally (.name f.atom))], f.next + 1⟩

/-! ### Counter and name-bound bookkeeping -/

theorem flattenL_le (C : Concept) : ∀ n, n ≤ (flattenL C n).next := by
  induction C with
  | name b => intro n; simp only [flattenL]; omega
  | meet C D ihC ihD =>
      intro n
      simp only [flattenL]
      have h1 := ihC n
      have h2 := ihD (flattenL C n).next
      omega
  | some r C ihC =>
      intro n
      simp only [flattenL]
      have h1 := ihC n
      omega
  | top => intro n; simp only [flattenL]; omega
  | next C ihC =>
      intro n
      simp only [flattenL]
      have h1 := ihC n
      omega
  | luntil C D ihC ihD =>
      intro n
      simp only [flattenL]
      have h1 := ihC n
      have h2 := ihD (flattenL C n).next
      omega
  | globally C _ => intro n; simp only [flattenL]; omega

theorem flattenR_le (C : Concept) : ∀ n, n ≤ (flattenR C n).next := by
  induction C with
  | name b => intro n; simp only [flattenR]; omega
  | meet C D ihC ihD =>
      intro n
      simp only [flattenR]
      have h1 := ihC n
      have h2 := ihD (flattenR C n).next
      omega
  | some r C ihC =>
      intro n
      simp only [flattenR]
      have h1 := ihC n
      omega
  | top => intro n; simp only [flattenR]; omega
  | next C ihC =>
      intro n
      simp only [flattenR]
      have h1 := ihC n
      omega
  | luntil C D _ _ => intro n; simp only [flattenR]; omega
  | globally C ihC =>
      intro n
      simp only [flattenR]
      have h1 := ihC n
      omega

theorem flattenL_atom_lt (C : Concept) :
    ∀ n, C.namesBelow n → (flattenL C n).atom < (flattenL C n).next := by
  induction C with
  | name b => intro n h; simp only [flattenL]; exact h b rfl
  | meet C D ihC ihD => intro n h; simp only [flattenL]; omega
  | some r C ihC => intro n h; simp only [flattenL]; omega
  | top => intro n h; simp only [flattenL]; omega
  | next C _ => intro n h; simp only [flattenL]; omega
  | luntil C D _ _ => intro n h; simp only [flattenL]; omega
  | globally C _ => intro n h; simp only [flattenL]; omega

theorem flattenR_atom_lt (C : Concept) :
    ∀ n, C.namesBelow n → (flattenR C n).atom < (flattenR C n).next := by
  induction C with
  | name b => intro n h; simp only [flattenR]; exact h b rfl
  | meet C D ihC ihD => intro n h; simp only [flattenR]; omega
  | some r C ihC => intro n h; simp only [flattenR]; omega
  | top => intro n h; simp only [flattenR]; omega
  | next C _ => intro n h; simp only [flattenR]; omega
  | luntil C D _ _ => intro n h; simp only [flattenR]; omega
  | globally C _ => intro n h; simp only [flattenR]; omega

theorem flattenL_axs_below (C : Concept) :
    ∀ n, C.namesBelow n → (flattenL C n).axs.namesBelow (flattenL C n).next := by
  induction C with
  | name b => intro n h ax hax; simp only [flattenL] at hax; exact absurd hax (List.not_mem_nil)
  | meet C D ihC ihD =>
      intro n h ax hax
      have hC : C.namesBelow n := fun b hb => h b (Or.inl hb)
      have hD : D.namesBelow (flattenL C n).next :=
        Concept.namesBelow.mono (fun b hb => h b (Or.inr hb)) (flattenL_le C n)
      have haC := flattenL_atom_lt C n hC
      have haD := flattenL_atom_lt D (flattenL C n).next hD
      have hle1 := flattenL_le C n
      have hle2 := flattenL_le D (flattenL C n).next
      simp only [flattenL] at hax ⊢
      rcases List.mem_append.mp hax with hax | hax
      · rcases List.mem_append.mp hax with hax | hax
        · exact Axiom.namesBelow.mono (ihC n hC ax hax) (by omega)
        · exact Axiom.namesBelow.mono (ihD (flattenL C n).next hD ax hax) (by omega)
      · simp only [List.mem_singleton] at hax
        subst hax
        refine ⟨fun b hb => ?_, fun b hb => ?_⟩
        · rcases hb with hb | hb
          · simp only [Concept.mentions] at hb; subst hb; omega
          · simp only [Concept.mentions] at hb; subst hb; omega
        · simp only [Concept.mentions] at hb; subst hb; omega
  | some r C ihC =>
      intro n h ax hax
      have haC := flattenL_atom_lt C n h
      have hle1 := flattenL_le C n
      simp only [flattenL] at hax ⊢
      rcases List.mem_append.mp hax with hax | hax
      · exact Axiom.namesBelow.mono (ihC n h ax hax) (by omega)
      · simp only [List.mem_singleton] at hax
        subst hax
        refine ⟨fun b hb => ?_, fun b hb => ?_⟩
        · simp only [Concept.mentions] at hb; subst hb; omega
        · simp only [Concept.mentions] at hb; subst hb; omega
  | top =>
      intro n h ax hax
      simp only [flattenL, List.mem_singleton] at hax ⊢
      subst hax
      refine ⟨fun b hb => ?_, fun b hb => ?_⟩
      · simp only [Concept.mentions] at hb
      · simp only [Concept.mentions] at hb; subst hb; omega
  | next C ihC =>
      intro n h ax hax
      have hCb : C.namesBelow n := fun b hb => h b hb
      have haC := flattenL_atom_lt C n hCb
      have hle1 := flattenL_le C n
      simp only [flattenL] at hax ⊢
      rcases List.mem_append.mp hax with hax | hax
      · exact Axiom.namesBelow.mono (ihC n hCb ax hax) (by omega)
      · simp only [List.mem_singleton] at hax
        subst hax
        refine ⟨fun b hb => ?_, fun b hb => ?_⟩
        · simp only [Concept.mentions] at hb; subst hb; omega
        · simp only [Concept.mentions] at hb; subst hb; omega
  | luntil C D ihC ihD =>
      intro n h ax hax
      have hC : C.namesBelow n := fun b hb => h b (Or.inl hb)
      have hD : D.namesBelow (flattenL C n).next :=
        Concept.namesBelow.mono (fun b hb => h b (Or.inr hb)) (flattenL_le C n)
      have haC := flattenL_atom_lt C n hC
      have haD := flattenL_atom_lt D (flattenL C n).next hD
      have hle1 := flattenL_le C n
      have hle2 := flattenL_le D (flattenL C n).next
      simp only [flattenL] at hax ⊢
      rcases List.mem_append.mp hax with hax | hax
      · rcases List.mem_append.mp hax with hax | hax
        · exact Axiom.namesBelow.mono (ihC n hC ax hax) (by omega)
        · exact Axiom.namesBelow.mono (ihD (flattenL C n).next hD ax hax) (by omega)
      · simp only [List.mem_singleton] at hax
        subst hax
        refine ⟨fun b hb => ?_, fun b hb => ?_⟩
        · rcases hb with hb | hb
          · simp only [Concept.mentions] at hb; subst hb; omega
          · simp only [Concept.mentions] at hb; subst hb; omega
        · simp only [Concept.mentions] at hb; subst hb; omega
  | globally C _ =>
      intro n h ax hax; simp only [flattenL] at hax; exact absurd hax (List.not_mem_nil)

theorem flattenR_axs_below (C : Concept) :
    ∀ n, C.namesBelow n → (flattenR C n).axs.namesBelow (flattenR C n).next := by
  induction C with
  | name b => intro n h ax hax; simp only [flattenR] at hax; exact absurd hax (List.not_mem_nil)
  | meet C D ihC ihD =>
      intro n h ax hax
      have hC : C.namesBelow n := fun b hb => h b (Or.inl hb)
      have hD : D.namesBelow (flattenR C n).next :=
        Concept.namesBelow.mono (fun b hb => h b (Or.inr hb)) (flattenR_le C n)
      have haC := flattenR_atom_lt C n hC
      have haD := flattenR_atom_lt D (flattenR C n).next hD
      have hle1 := flattenR_le C n
      have hle2 := flattenR_le D (flattenR C n).next
      simp only [flattenR] at hax ⊢
      rcases List.mem_append.mp hax with hax | hax
      · rcases List.mem_append.mp hax with hax | hax
        · exact Axiom.namesBelow.mono (ihC n hC ax hax) (by omega)
        · exact Axiom.namesBelow.mono (ihD (flattenR C n).next hD ax hax) (by omega)
      · rcases List.mem_cons.mp hax with hax | hax
        · subst hax
          refine ⟨fun b hb => ?_, fun b hb => ?_⟩
          · simp only [Concept.mentions] at hb; subst hb; omega
          · simp only [Concept.mentions] at hb; subst hb; omega
        · simp only [List.mem_singleton] at hax
          subst hax
          refine ⟨fun b hb => ?_, fun b hb => ?_⟩
          · simp only [Concept.mentions] at hb; subst hb; omega
          · simp only [Concept.mentions] at hb; subst hb; omega
  | some r C ihC =>
      intro n h ax hax
      have haC := flattenR_atom_lt C n h
      have hle1 := flattenR_le C n
      simp only [flattenR] at hax ⊢
      rcases List.mem_append.mp hax with hax | hax
      · exact Axiom.namesBelow.mono (ihC n h ax hax) (by omega)
      · simp only [List.mem_singleton] at hax
        subst hax
        refine ⟨fun b hb => ?_, fun b hb => ?_⟩
        · simp only [Concept.mentions] at hb; subst hb; omega
        · simp only [Concept.mentions] at hb; subst hb; omega
  | top => intro n h ax hax; simp only [flattenR] at hax; exact absurd hax (List.not_mem_nil)
  | next C ihC =>
      intro n h ax hax
      have hCb : C.namesBelow n := fun b hb => h b hb
      have haC := flattenR_atom_lt C n hCb
      have hle1 := flattenR_le C n
      simp only [flattenR] at hax ⊢
      rcases List.mem_append.mp hax with hax | hax
      · exact Axiom.namesBelow.mono (ihC n hCb ax hax) (by omega)
      · simp only [List.mem_singleton] at hax
        subst hax
        refine ⟨fun b hb => ?_, fun b hb => ?_⟩
        · simp only [Concept.mentions] at hb; subst hb; omega
        · simp only [Concept.mentions] at hb; subst hb; omega
  | luntil C D _ _ =>
      intro n h ax hax; simp only [flattenR] at hax; exact absurd hax (List.not_mem_nil)
  | globally C ihC =>
      intro n h ax hax
      have hCb : C.namesBelow n := fun b hb => h b hb
      have haC := flattenR_atom_lt C n hCb
      have hle1 := flattenR_le C n
      simp only [flattenR] at hax ⊢
      rcases List.mem_append.mp hax with hax | hax
      · exact Axiom.namesBelow.mono (ihC n hCb ax hax) (by omega)
      · simp only [List.mem_singleton] at hax
        subst hax
        refine ⟨fun b hb => ?_, fun b hb => ?_⟩
        · simp only [Concept.mentions] at hb; subst hb; omega
        · simp only [Concept.mentions] at hb; subst hb; omega

/-! ### NF shapes -/

/-- The L1 target shape. -/
def NFAxiom (ax : Axiom) : Prop :=
  (∃ C D, ax = .gci C D ∧ LhsNF C ∧ RhsNF D) ∨ ∃ r s u, ax = .ri r s u

theorem flattenL_nf {C : Concept} (hEL : NegConcept C) :
    ∀ n, ∀ ax ∈ (flattenL C n).axs, NFAxiom ax := by
  induction hEL with
  | top =>
      intro n ax hax
      simp only [flattenL, List.mem_singleton] at hax
      subst hax
      exact Or.inl ⟨_, _, rfl, LhsNF.top, RhsNF.name⟩
  | @next C _ ihC =>
      intro n ax hax
      simp only [flattenL] at hax
      rcases List.mem_append.mp hax with hax | hax
      · exact ihC n ax hax
      · simp only [List.mem_singleton] at hax
        subst hax
        exact Or.inl ⟨_, _, rfl, LhsNF.next LhsNF.name, RhsNF.name⟩
  | @luntil C D _ _ ihC ihD =>
      intro n ax hax
      simp only [flattenL] at hax
      rcases List.mem_append.mp hax with hax | hax
      · rcases List.mem_append.mp hax with hax | hax
        · exact ihC n ax hax
        · exact ihD (flattenL C n).next ax hax
      · simp only [List.mem_singleton] at hax
        subst hax
        exact Or.inl ⟨_, _, rfl, LhsNF.luntil LhsNF.name LhsNF.name, RhsNF.name⟩
  | name => intro n ax hax; simp only [flattenL] at hax; exact absurd hax (List.not_mem_nil)
  | @meet C D _ _ ihC ihD =>
      intro n ax hax
      simp only [flattenL] at hax
      rcases List.mem_append.mp hax with hax | hax
      · rcases List.mem_append.mp hax with hax | hax
        · exact ihC n ax hax
        · exact ihD (flattenL C n).next ax hax
      · simp only [List.mem_singleton] at hax
        subst hax
        exact Or.inl ⟨_, _, rfl, LhsNF.meet LhsNF.name LhsNF.name, RhsNF.name⟩
  | @some C r _ ihC =>
      intro n ax hax
      simp only [flattenL] at hax
      rcases List.mem_append.mp hax with hax | hax
      · exact ihC n ax hax
      · simp only [List.mem_singleton] at hax
        subst hax
        exact Or.inl ⟨_, _, rfl, LhsNF.some LhsNF.name, RhsNF.name⟩

theorem flattenR_nf {C : Concept} (hEL : PosConcept C) :
    ∀ n, ∀ ax ∈ (flattenR C n).axs, NFAxiom ax := by
  induction hEL with
  | top => intro n ax hax; simp only [flattenR] at hax; exact absurd hax (List.not_mem_nil)
  | @next C _ ihC =>
      intro n ax hax
      simp only [flattenR] at hax
      rcases List.mem_append.mp hax with hax | hax
      · exact ihC n ax hax
      · simp only [List.mem_singleton] at hax
        subst hax
        exact Or.inl ⟨_, _, rfl, LhsNF.name, RhsNF.next RhsNF.name⟩
  | @globally C _ ihC =>
      intro n ax hax
      simp only [flattenR] at hax
      rcases List.mem_append.mp hax with hax | hax
      · exact ihC n ax hax
      · simp only [List.mem_singleton] at hax
        subst hax
        exact Or.inl ⟨_, _, rfl, LhsNF.name, RhsNF.glob RhsNF.name⟩
  | name => intro n ax hax; simp only [flattenR] at hax; exact absurd hax (List.not_mem_nil)
  | @meet C D _ _ ihC ihD =>
      intro n ax hax
      simp only [flattenR] at hax
      rcases List.mem_append.mp hax with hax | hax
      · rcases List.mem_append.mp hax with hax | hax
        · exact ihC n ax hax
        · exact ihD (flattenR C n).next ax hax
      · rcases List.mem_cons.mp hax with hax | hax
        · subst hax; exact Or.inl ⟨_, _, rfl, LhsNF.name, RhsNF.name⟩
        · simp only [List.mem_singleton] at hax
          subst hax; exact Or.inl ⟨_, _, rfl, LhsNF.name, RhsNF.name⟩
  | @some C r _ ihC =>
      intro n ax hax
      simp only [flattenR] at hax
      rcases List.mem_append.mp hax with hax | hax
      · exact ihC n ax hax
      · simp only [List.mem_singleton] at hax
        subst hax
        exact Or.inl ⟨_, _, rfl, LhsNF.name, RhsNF.some RhsNF.name⟩

/-! ### Soundness: models of the emitted axioms satisfy the represented inclusion -/

theorem flattenL_sound {C : Concept} (hEL : NegConcept C) (I : TemporalInterp Δ) :
    ∀ n, models I (flattenL C n).axs →
      ∀ t d, ext I C t d → ext I (.name (flattenL C n).atom) t d := by
  induction hEL with
  | top =>
      intro n hm t d _
      simp only [flattenL] at hm ⊢
      exact (hm _ (List.mem_singleton.mpr rfl)) t d trivial
  | @next C _ ihC =>
      intro n hm t d hext
      simp only [flattenL] at hm ⊢
      rw [models_append] at hm
      obtain ⟨hmf, hmax⟩ := hm
      have h1 := ihC n hmf (t + 1) d hext
      exact (hmax _ (List.mem_singleton.mpr rfl)) t d h1
  | @luntil C D _ _ ihC ihD =>
      intro n hm t d hext
      simp only [flattenL] at hm ⊢
      rw [models_append, models_append] at hm
      obtain ⟨⟨hmf, hmg⟩, hmax⟩ := hm
      obtain ⟨t', ht', hD, hC⟩ := hext
      refine (hmax _ (List.mem_singleton.mpr rfl)) t d ?_
      exact ⟨t', ht', ihD (flattenL C n).next hmg t' d hD,
             fun t'' h1 h2 => ihC n hmf t'' d (hC t'' h1 h2)⟩
  | @name b =>
      intro n _ t d h
      simp only [flattenL]
      exact h
  | @meet C D _ _ ihC ihD =>
      intro n hm t d hext
      simp only [flattenL] at hm ⊢
      rw [models_append, models_append] at hm
      obtain ⟨⟨hmf, hmg⟩, hmax⟩ := hm
      obtain ⟨he1, he2⟩ := hext
      have h1 := ihC n hmf t d he1
      have h2 := ihD (flattenL C n).next hmg t d he2
      exact (hmax _ (List.mem_singleton.mpr rfl)) t d ⟨h1, h2⟩
  | @some C r _ ihC =>
      intro n hm t d hext
      simp only [flattenL] at hm ⊢
      rw [models_append] at hm
      obtain ⟨hmf, hmax⟩ := hm
      obtain ⟨e, hr, he⟩ := hext
      exact (hmax _ (List.mem_singleton.mpr rfl)) t d ⟨e, hr, ihC n hmf t e he⟩

theorem flattenR_sound {C : Concept} (hEL : PosConcept C) (I : TemporalInterp Δ) :
    ∀ n, models I (flattenR C n).axs →
      ∀ t d, ext I (.name (flattenR C n).atom) t d → ext I C t d := by
  induction hEL with
  | top =>
      intro n _ t d _
      exact trivial
  | @next C _ ihC =>
      intro n hm t d hat
      simp only [flattenR] at hm hat
      rw [models_append] at hm
      obtain ⟨hmf, hmax⟩ := hm
      have h1 := (hmax _ (List.mem_singleton.mpr rfl)) t d hat
      exact ihC n hmf (t + 1) d h1
  | @globally C _ ihC =>
      intro n hm t d hat
      simp only [flattenR] at hm hat
      rw [models_append] at hm
      obtain ⟨hmf, hmax⟩ := hm
      have h1 := (hmax _ (List.mem_singleton.mpr rfl)) t d hat
      intro t' ht'
      exact ihC n hmf t' d (h1 t' ht')
  | @name b =>
      intro n _ t d h
      simp only [flattenR] at h
      exact h
  | @meet C D _ _ ihC ihD =>
      intro n hm t d hat
      simp only [flattenR] at hm hat
      rw [models_append, models_append] at hm
      obtain ⟨⟨hmf, hmg⟩, hmax⟩ := hm
      have hax1 := hmax _ (List.mem_cons_self ..)
      have hax2 := hmax _ (List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl)))
      exact ⟨ihC n hmf t d (hax1 t d hat), ihD (flattenR C n).next hmg t d (hax2 t d hat)⟩
  | @some C r _ ihC =>
      intro n hm t d hat
      simp only [flattenR] at hm hat
      rw [models_append] at hm
      obtain ⟨hmf, hmax⟩ := hm
      obtain ⟨e, hr, he⟩ := (hmax _ (List.mem_singleton.mpr rfl)) t d hat
      exact ⟨e, hr, ihC n hmf t e he⟩

/-! ### Completeness: every model extends to a model of the emitted axioms

    The fresh atoms are interpreted as the exact extensions of the sub-concepts
    they name (iterated `defineInterp`), so every emitted axiom holds with
    equality and the original interpretation is untouched below `n`. -/

theorem flattenL_complete {C : Concept} (hEL : NegConcept C) :
    ∀ n (I : TemporalInterp Δ), C.namesBelow n →
      ∃ I' : TemporalInterp Δ,
        AgreeBelow I I' n ∧
        models I' (flattenL C n).axs ∧
        (∀ t d, ext I' (.name (flattenL C n).atom) t d ↔ ext I' C t d) := by
  induction hEL with
  | top =>
      intro n I _
      have hEm : ¬ (Concept.top).mentions n := fun hm => hm
      have hagD : AgreeBelow I (defineInterp I n Concept.top) n :=
        agree_defineInterp I n Concept.top (Nat.le_refl n)
      have hdef := defineInterp_def_holds I n Concept.top hEm
      refine ⟨defineInterp I n Concept.top, hagD, ?_, ?_⟩
      · intro ax hax
        simp only [flattenL, List.mem_singleton] at hax
        subst hax
        exact hdef.2
      · intro t d
        simp only [flattenL]
        exact ⟨fun hh => hdef.1 t d hh, fun hh => hdef.2 t d hh⟩
  | @next C _ ihC =>
      intro n I h
      have hCb : C.namesBelow n := fun b hb => h b hb
      obtain ⟨I₁, hag₁, hm₁, hat₁⟩ := ihC n I hCb
      have hnn1 := flattenL_le C n
      have haC := flattenL_atom_lt C n hCb
      have hCb1 : C.namesBelow (flattenL C n).next := hCb.mono hnn1
      have hsb1 : (Concept.next C).namesBelow (flattenL C n).next :=
        fun b hb => hCb1 b hb
      have hEm : ¬ (Concept.next C).mentions (flattenL C n).next :=
        not_mentions_of_namesBelow hsb1 (Nat.le_refl _)
      have hagD : AgreeBelow I₁
          (defineInterp I₁ (flattenL C n).next (Concept.next C)) (flattenL C n).next :=
        agree_defineInterp I₁ _ _ (Nat.le_refl _)
      have hdef := defineInterp_def_holds I₁ (flattenL C n).next (Concept.next C) hEm
      have hnameC1 : (Concept.name (flattenL C n).atom).namesBelow (flattenL C n).next := by
        intro b hb; simp only [Concept.mentions] at hb; subst hb; omega
      have hat₁' : ∀ t d,
          ext (defineInterp I₁ (flattenL C n).next (Concept.next C))
            (.name (flattenL C n).atom) t d ↔
          ext (defineInterp I₁ (flattenL C n).next (Concept.next C)) C t d := by
        intro t d
        rw [ext_agree hagD _ hnameC1 t d, ext_agree hagD C hCb1 t d]
        exact hat₁ t d
      refine ⟨defineInterp I₁ (flattenL C n).next (Concept.next C), ?_, ?_, ?_⟩
      · exact hag₁.chain hagD hnn1
      · simp only [flattenL]
        rw [models_append]
        refine ⟨?_, ?_⟩
        · rw [models_agree hagD (flattenL_axs_below C n hCb)]
          exact hm₁
        · intro ax hax
          simp only [List.mem_singleton] at hax
          subst hax
          intro t d hnext
          exact hdef.2 t d ((hat₁' (t + 1) d).mp hnext)
      · intro t d
        simp only [flattenL]
        exact ⟨fun hh => hdef.1 t d hh, fun hh => hdef.2 t d hh⟩
  | @luntil C D _ _ ihC ihD =>
      intro n I h
      have hCb : C.namesBelow n := fun b hb => h b (Or.inl hb)
      have hDb : D.namesBelow n := fun b hb => h b (Or.inr hb)
      have hnn1 : n ≤ (flattenL C n).next := flattenL_le C n
      have hDb1 : D.namesBelow (flattenL C n).next := hDb.mono hnn1
      obtain ⟨I₁, hag₁, hm₁, hat₁⟩ := ihC n I hCb
      obtain ⟨I₂, hag₂, hm₂, hat₂⟩ := ihD (flattenL C n).next I₁ hDb1
      have hn12 := flattenL_le D (flattenL C n).next
      have haC := flattenL_atom_lt C n hCb
      have haD := flattenL_atom_lt D (flattenL C n).next hDb1
      have hCb1 : C.namesBelow (flattenL C n).next := hCb.mono hnn1
      have hCb2 : C.namesBelow (flattenL D (flattenL C n).next).next := hCb1.mono hn12
      have hDb2 : D.namesBelow (flattenL D (flattenL C n).next).next := hDb1.mono hn12
      have huntb : (Concept.luntil C D).namesBelow (flattenL D (flattenL C n).next).next := by
        intro b hb
        rcases hb with hb | hb
        · exact hCb2 b hb
        · exact hDb2 b hb
      have hEm : ¬ (Concept.luntil C D).mentions (flattenL D (flattenL C n).next).next :=
        not_mentions_of_namesBelow huntb (Nat.le_refl _)
      have hagD : AgreeBelow I₂
          (defineInterp I₂ (flattenL D (flattenL C n).next).next (Concept.luntil C D))
          (flattenL D (flattenL C n).next).next :=
        agree_defineInterp I₂ _ _ (Nat.le_refl _)
      have hdef := defineInterp_def_holds I₂ (flattenL D (flattenL C n).next).next
        (Concept.luntil C D) hEm
      have hnameC1 : (Concept.name (flattenL C n).atom).namesBelow (flattenL C n).next := by
        intro b hb; simp only [Concept.mentions] at hb; subst hb; omega
      have hnameC2 : (Concept.name (flattenL C n).atom).namesBelow
          (flattenL D (flattenL C n).next).next := by
        intro b hb; simp only [Concept.mentions] at hb; subst hb; omega
      have hnameD2 : (Concept.name (flattenL D (flattenL C n).next).atom).namesBelow
          (flattenL D (flattenL C n).next).next := by
        intro b hb; simp only [Concept.mentions] at hb; subst hb; omega
      have hat₁' : ∀ t d,
          ext (defineInterp I₂ (flattenL D (flattenL C n).next).next (Concept.luntil C D))
            (.name (flattenL C n).atom) t d ↔
          ext (defineInterp I₂ (flattenL D (flattenL C n).next).next (Concept.luntil C D))
            C t d := by
        intro t d
        rw [ext_agree hagD _ hnameC2 t d, ext_agree hagD C hCb2 t d,
            ext_agree hag₂ _ hnameC1 t d, ext_agree hag₂ C hCb1 t d]
        exact hat₁ t d
      have hat₂' : ∀ t d,
          ext (defineInterp I₂ (flattenL D (flattenL C n).next).next (Concept.luntil C D))
            (.name (flattenL D (flattenL C n).next).atom) t d ↔
          ext (defineInterp I₂ (flattenL D (flattenL C n).next).next (Concept.luntil C D))
            D t d := by
        intro t d
        rw [ext_agree hagD _ hnameD2 t d, ext_agree hagD D hDb2 t d]
        exact hat₂ t d
      refine ⟨defineInterp I₂ (flattenL D (flattenL C n).next).next (Concept.luntil C D),
              ?_, ?_, ?_⟩
      · exact (hag₁.chain hag₂ hnn1).chain hagD (Nat.le_trans hnn1 hn12)
      · simp only [flattenL]
        rw [models_append, models_append]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · rw [models_agree hagD ((flattenL_axs_below C n hCb).mono hn12),
              models_agree hag₂ (flattenL_axs_below C n hCb)]
          exact hm₁
        · rw [models_agree hagD (flattenL_axs_below D (flattenL C n).next hDb1)]
          exact hm₂
        · intro ax hax
          simp only [List.mem_singleton] at hax
          subst hax
          intro t d hu
          obtain ⟨t', ht', hDt, hCt⟩ := hu
          exact hdef.2 t d ⟨t', ht', (hat₂' t' d).mp hDt,
                            fun t'' h1 h2 => (hat₁' t'' d).mp (hCt t'' h1 h2)⟩
      · intro t d
        simp only [flattenL]
        exact ⟨fun hh => hdef.1 t d hh, fun hh => hdef.2 t d hh⟩
  | @name b =>
      intro n I _
      refine ⟨I, AgreeBelow.rfl I n, ?_, ?_⟩
      · intro ax hax
        simp only [flattenL] at hax
        exact absurd hax (List.not_mem_nil)
      · intro t d
        simp only [flattenL]
  | @meet C D _ _ ihC ihD =>
      intro n I h
      have hCb : C.namesBelow n := fun b hb => h b (Or.inl hb)
      have hDb : D.namesBelow n := fun b hb => h b (Or.inr hb)
      have hnn1 : n ≤ (flattenL C n).next := flattenL_le C n
      have hDb1 : D.namesBelow (flattenL C n).next := hDb.mono hnn1
      obtain ⟨I₁, hag₁, hm₁, hat₁⟩ := ihC n I hCb
      obtain ⟨I₂, hag₂, hm₂, hat₂⟩ := ihD (flattenL C n).next I₁ hDb1
      have hn12 := flattenL_le D (flattenL C n).next
      have haC := flattenL_atom_lt C n hCb
      have haD := flattenL_atom_lt D (flattenL C n).next hDb1
      have hCb1 : C.namesBelow (flattenL C n).next := hCb.mono hnn1
      have hCb2 : C.namesBelow (flattenL D (flattenL C n).next).next := hCb1.mono hn12
      have hDb2 : D.namesBelow (flattenL D (flattenL C n).next).next := hDb1.mono hn12
      have hmeetb : (Concept.meet C D).namesBelow (flattenL D (flattenL C n).next).next := by
        intro b hb
        rcases hb with hb | hb
        · exact hCb2 b hb
        · exact hDb2 b hb
      have hEm : ¬ (Concept.meet C D).mentions (flattenL D (flattenL C n).next).next :=
        not_mentions_of_namesBelow hmeetb (Nat.le_refl _)
      have hagD : AgreeBelow I₂
          (defineInterp I₂ (flattenL D (flattenL C n).next).next (Concept.meet C D))
          (flattenL D (flattenL C n).next).next :=
        agree_defineInterp I₂ _ _ (Nat.le_refl _)
      have hdef := defineInterp_def_holds I₂ (flattenL D (flattenL C n).next).next
        (Concept.meet C D) hEm
      have hnameC1 : (Concept.name (flattenL C n).atom).namesBelow (flattenL C n).next := by
        intro b hb; simp only [Concept.mentions] at hb; subst hb; omega
      have hnameC2 : (Concept.name (flattenL C n).atom).namesBelow
          (flattenL D (flattenL C n).next).next := by
        intro b hb; simp only [Concept.mentions] at hb; subst hb; omega
      have hnameD2 : (Concept.name (flattenL D (flattenL C n).next).atom).namesBelow
          (flattenL D (flattenL C n).next).next := by
        intro b hb; simp only [Concept.mentions] at hb; subst hb; omega
      have hat₁' : ∀ t d,
          ext (defineInterp I₂ (flattenL D (flattenL C n).next).next (Concept.meet C D))
            (.name (flattenL C n).atom) t d ↔
          ext (defineInterp I₂ (flattenL D (flattenL C n).next).next (Concept.meet C D))
            C t d := by
        intro t d
        rw [ext_agree hagD _ hnameC2 t d, ext_agree hagD C hCb2 t d,
            ext_agree hag₂ _ hnameC1 t d, ext_agree hag₂ C hCb1 t d]
        exact hat₁ t d
      have hat₂' : ∀ t d,
          ext (defineInterp I₂ (flattenL D (flattenL C n).next).next (Concept.meet C D))
            (.name (flattenL D (flattenL C n).next).atom) t d ↔
          ext (defineInterp I₂ (flattenL D (flattenL C n).next).next (Concept.meet C D))
            D t d := by
        intro t d
        rw [ext_agree hagD _ hnameD2 t d, ext_agree hagD D hDb2 t d]
        exact hat₂ t d
      refine ⟨defineInterp I₂ (flattenL D (flattenL C n).next).next (Concept.meet C D),
              ?_, ?_, ?_⟩
      · exact (hag₁.chain hag₂ hnn1).chain hagD (Nat.le_trans hnn1 hn12)
      · simp only [flattenL]
        rw [models_append, models_append]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · rw [models_agree hagD ((flattenL_axs_below C n hCb).mono hn12),
              models_agree hag₂ (flattenL_axs_below C n hCb)]
          exact hm₁
        · rw [models_agree hagD (flattenL_axs_below D (flattenL C n).next hDb1)]
          exact hm₂
        · intro ax hax
          simp only [List.mem_singleton] at hax
          subst hax
          intro t d hmeet
          obtain ⟨hx, hy⟩ := hmeet
          exact hdef.2 t d ⟨(hat₁' t d).mp hx, (hat₂' t d).mp hy⟩
      · intro t d
        simp only [flattenL]
        exact ⟨fun hh => hdef.1 t d hh, fun hh => hdef.2 t d hh⟩
  | @some C r _ ihC =>
      intro n I h
      have hCb : C.namesBelow n := fun b hb => h b hb
      obtain ⟨I₁, hag₁, hm₁, hat₁⟩ := ihC n I hCb
      have hnn1 := flattenL_le C n
      have haC := flattenL_atom_lt C n hCb
      have hCb1 : C.namesBelow (flattenL C n).next := hCb.mono hnn1
      have hsb1 : (Concept.some r C).namesBelow (flattenL C n).next :=
        fun b hb => hCb1 b hb
      have hEm : ¬ (Concept.some r C).mentions (flattenL C n).next :=
        not_mentions_of_namesBelow hsb1 (Nat.le_refl _)
      have hagD : AgreeBelow I₁
          (defineInterp I₁ (flattenL C n).next (Concept.some r C)) (flattenL C n).next :=
        agree_defineInterp I₁ _ _ (Nat.le_refl _)
      have hdef := defineInterp_def_holds I₁ (flattenL C n).next (Concept.some r C) hEm
      have hnameC1 : (Concept.name (flattenL C n).atom).namesBelow (flattenL C n).next := by
        intro b hb; simp only [Concept.mentions] at hb; subst hb; omega
      have hat₁' : ∀ t d,
          ext (defineInterp I₁ (flattenL C n).next (Concept.some r C))
            (.name (flattenL C n).atom) t d ↔
          ext (defineInterp I₁ (flattenL C n).next (Concept.some r C)) C t d := by
        intro t d
        rw [ext_agree hagD _ hnameC1 t d, ext_agree hagD C hCb1 t d]
        exact hat₁ t d
      refine ⟨defineInterp I₁ (flattenL C n).next (Concept.some r C), ?_, ?_, ?_⟩
      · exact hag₁.chain hagD hnn1
      · simp only [flattenL]
        rw [models_append]
        refine ⟨?_, ?_⟩
        · rw [models_agree hagD (flattenL_axs_below C n hCb)]
          exact hm₁
        · intro ax hax
          simp only [List.mem_singleton] at hax
          subst hax
          intro t d hsome
          obtain ⟨e, hr, he⟩ := hsome
          exact hdef.2 t d ⟨e, hr, (hat₁' t e).mp he⟩
      · intro t d
        simp only [flattenL]
        exact ⟨fun hh => hdef.1 t d hh, fun hh => hdef.2 t d hh⟩

theorem flattenR_complete {C : Concept} (hEL : PosConcept C) :
    ∀ n (I : TemporalInterp Δ), C.namesBelow n →
      ∃ I' : TemporalInterp Δ,
        AgreeBelow I I' n ∧
        models I' (flattenR C n).axs ∧
        (∀ t d, ext I' (.name (flattenR C n).atom) t d ↔ ext I' C t d) := by
  induction hEL with
  | top =>
      intro n I _
      have hEm : ¬ (Concept.top).mentions n := fun hm => hm
      have hagD : AgreeBelow I (defineInterp I n Concept.top) n :=
        agree_defineInterp I n Concept.top (Nat.le_refl n)
      have hdef := defineInterp_def_holds I n Concept.top hEm
      refine ⟨defineInterp I n Concept.top, hagD, ?_, ?_⟩
      · intro ax hax
        simp only [flattenR] at hax
        exact absurd hax (List.not_mem_nil)
      · intro t d
        simp only [flattenR]
        exact ⟨fun hh => hdef.1 t d hh, fun hh => hdef.2 t d hh⟩
  | @next C _ ihC =>
      intro n I h
      have hCb : C.namesBelow n := fun b hb => h b hb
      obtain ⟨I₁, hag₁, hm₁, hat₁⟩ := ihC n I hCb
      have hnn1 := flattenR_le C n
      have haC := flattenR_atom_lt C n hCb
      have hCb1 : C.namesBelow (flattenR C n).next := hCb.mono hnn1
      have hsb1 : (Concept.next C).namesBelow (flattenR C n).next :=
        fun b hb => hCb1 b hb
      have hEm : ¬ (Concept.next C).mentions (flattenR C n).next :=
        not_mentions_of_namesBelow hsb1 (Nat.le_refl _)
      have hagD : AgreeBelow I₁
          (defineInterp I₁ (flattenR C n).next (Concept.next C)) (flattenR C n).next :=
        agree_defineInterp I₁ _ _ (Nat.le_refl _)
      have hdef := defineInterp_def_holds I₁ (flattenR C n).next (Concept.next C) hEm
      have hnameC1 : (Concept.name (flattenR C n).atom).namesBelow (flattenR C n).next := by
        intro b hb; simp only [Concept.mentions] at hb; subst hb; omega
      have hat₁' : ∀ t d,
          ext (defineInterp I₁ (flattenR C n).next (Concept.next C))
            (.name (flattenR C n).atom) t d ↔
          ext (defineInterp I₁ (flattenR C n).next (Concept.next C)) C t d := by
        intro t d
        rw [ext_agree hagD _ hnameC1 t d, ext_agree hagD C hCb1 t d]
        exact hat₁ t d
      refine ⟨defineInterp I₁ (flattenR C n).next (Concept.next C), ?_, ?_, ?_⟩
      · exact hag₁.chain hagD hnn1
      · simp only [flattenR]
        rw [models_append]
        refine ⟨?_, ?_⟩
        · rw [models_agree hagD (flattenR_axs_below C n hCb)]
          exact hm₁
        · intro ax hax
          simp only [List.mem_singleton] at hax
          subst hax
          intro t d hat
          exact (hat₁' (t + 1) d).mpr (hdef.1 t d hat)
      · intro t d
        simp only [flattenR]
        exact ⟨fun hh => hdef.1 t d hh, fun hh => hdef.2 t d hh⟩
  | @globally C _ ihC =>
      intro n I h
      have hCb : C.namesBelow n := fun b hb => h b hb
      obtain ⟨I₁, hag₁, hm₁, hat₁⟩ := ihC n I hCb
      have hnn1 := flattenR_le C n
      have haC := flattenR_atom_lt C n hCb
      have hCb1 : C.namesBelow (flattenR C n).next := hCb.mono hnn1
      have hsb1 : (Concept.globally C).namesBelow (flattenR C n).next :=
        fun b hb => hCb1 b hb
      have hEm : ¬ (Concept.globally C).mentions (flattenR C n).next :=
        not_mentions_of_namesBelow hsb1 (Nat.le_refl _)
      have hagD : AgreeBelow I₁
          (defineInterp I₁ (flattenR C n).next (Concept.globally C)) (flattenR C n).next :=
        agree_defineInterp I₁ _ _ (Nat.le_refl _)
      have hdef := defineInterp_def_holds I₁ (flattenR C n).next (Concept.globally C) hEm
      have hnameC1 : (Concept.name (flattenR C n).atom).namesBelow (flattenR C n).next := by
        intro b hb; simp only [Concept.mentions] at hb; subst hb; omega
      have hat₁' : ∀ t d,
          ext (defineInterp I₁ (flattenR C n).next (Concept.globally C))
            (.name (flattenR C n).atom) t d ↔
          ext (defineInterp I₁ (flattenR C n).next (Concept.globally C)) C t d := by
        intro t d
        rw [ext_agree hagD _ hnameC1 t d, ext_agree hagD C hCb1 t d]
        exact hat₁ t d
      refine ⟨defineInterp I₁ (flattenR C n).next (Concept.globally C), ?_, ?_, ?_⟩
      · exact hag₁.chain hagD hnn1
      · simp only [flattenR]
        rw [models_append]
        refine ⟨?_, ?_⟩
        · rw [models_agree hagD (flattenR_axs_below C n hCb)]
          exact hm₁
        · intro ax hax
          simp only [List.mem_singleton] at hax
          subst hax
          intro t d hat t' ht'
          exact (hat₁' t' d).mpr ((hdef.1 t d hat) t' ht')
      · intro t d
        simp only [flattenR]
        exact ⟨fun hh => hdef.1 t d hh, fun hh => hdef.2 t d hh⟩
  | @name b =>
      intro n I _
      refine ⟨I, AgreeBelow.rfl I n, ?_, ?_⟩
      · intro ax hax
        simp only [flattenR] at hax
        exact absurd hax (List.not_mem_nil)
      · intro t d
        simp only [flattenR]
  | @meet C D _ _ ihC ihD =>
      intro n I h
      have hCb : C.namesBelow n := fun b hb => h b (Or.inl hb)
      have hDb : D.namesBelow n := fun b hb => h b (Or.inr hb)
      have hnn1 : n ≤ (flattenR C n).next := flattenR_le C n
      have hDb1 : D.namesBelow (flattenR C n).next := hDb.mono hnn1
      obtain ⟨I₁, hag₁, hm₁, hat₁⟩ := ihC n I hCb
      obtain ⟨I₂, hag₂, hm₂, hat₂⟩ := ihD (flattenR C n).next I₁ hDb1
      have hn12 := flattenR_le D (flattenR C n).next
      have haC := flattenR_atom_lt C n hCb
      have haD := flattenR_atom_lt D (flattenR C n).next hDb1
      have hCb1 : C.namesBelow (flattenR C n).next := hCb.mono hnn1
      have hCb2 : C.namesBelow (flattenR D (flattenR C n).next).next := hCb1.mono hn12
      have hDb2 : D.namesBelow (flattenR D (flattenR C n).next).next := hDb1.mono hn12
      have hmeetb : (Concept.meet C D).namesBelow (flattenR D (flattenR C n).next).next := by
        intro b hb
        rcases hb with hb | hb
        · exact hCb2 b hb
        · exact hDb2 b hb
      have hEm : ¬ (Concept.meet C D).mentions (flattenR D (flattenR C n).next).next :=
        not_mentions_of_namesBelow hmeetb (Nat.le_refl _)
      have hagD : AgreeBelow I₂
          (defineInterp I₂ (flattenR D (flattenR C n).next).next (Concept.meet C D))
          (flattenR D (flattenR C n).next).next :=
        agree_defineInterp I₂ _ _ (Nat.le_refl _)
      have hdef := defineInterp_def_holds I₂ (flattenR D (flattenR C n).next).next
        (Concept.meet C D) hEm
      have hnameC1 : (Concept.name (flattenR C n).atom).namesBelow (flattenR C n).next := by
        intro b hb; simp only [Concept.mentions] at hb; subst hb; omega
      have hnameC2 : (Concept.name (flattenR C n).atom).namesBelow
          (flattenR D (flattenR C n).next).next := by
        intro b hb; simp only [Concept.mentions] at hb; subst hb; omega
      have hnameD2 : (Concept.name (flattenR D (flattenR C n).next).atom).namesBelow
          (flattenR D (flattenR C n).next).next := by
        intro b hb; simp only [Concept.mentions] at hb; subst hb; omega
      have hat₁' : ∀ t d,
          ext (defineInterp I₂ (flattenR D (flattenR C n).next).next (Concept.meet C D))
            (.name (flattenR C n).atom) t d ↔
          ext (defineInterp I₂ (flattenR D (flattenR C n).next).next (Concept.meet C D))
            C t d := by
        intro t d
        rw [ext_agree hagD _ hnameC2 t d, ext_agree hagD C hCb2 t d,
            ext_agree hag₂ _ hnameC1 t d, ext_agree hag₂ C hCb1 t d]
        exact hat₁ t d
      have hat₂' : ∀ t d,
          ext (defineInterp I₂ (flattenR D (flattenR C n).next).next (Concept.meet C D))
            (.name (flattenR D (flattenR C n).next).atom) t d ↔
          ext (defineInterp I₂ (flattenR D (flattenR C n).next).next (Concept.meet C D))
            D t d := by
        intro t d
        rw [ext_agree hagD _ hnameD2 t d, ext_agree hagD D hDb2 t d]
        exact hat₂ t d
      refine ⟨defineInterp I₂ (flattenR D (flattenR C n).next).next (Concept.meet C D),
              ?_, ?_, ?_⟩
      · exact (hag₁.chain hag₂ hnn1).chain hagD (Nat.le_trans hnn1 hn12)
      · simp only [flattenR]
        rw [models_append, models_append]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · rw [models_agree hagD ((flattenR_axs_below C n hCb).mono hn12),
              models_agree hag₂ (flattenR_axs_below C n hCb)]
          exact hm₁
        · rw [models_agree hagD (flattenR_axs_below D (flattenR C n).next hDb1)]
          exact hm₂
        · intro ax hax
          rcases List.mem_cons.mp hax with hax | hax
          · subst hax
            intro t d hat
            exact (hat₁' t d).mpr (hdef.1 t d hat).1
          · simp only [List.mem_singleton] at hax
            subst hax
            intro t d hat
            exact (hat₂' t d).mpr (hdef.1 t d hat).2
      · intro t d
        simp only [flattenR]
        exact ⟨fun hh => hdef.1 t d hh, fun hh => hdef.2 t d hh⟩
  | @some C r _ ihC =>
      intro n I h
      have hCb : C.namesBelow n := fun b hb => h b hb
      obtain ⟨I₁, hag₁, hm₁, hat₁⟩ := ihC n I hCb
      have hnn1 := flattenR_le C n
      have haC := flattenR_atom_lt C n hCb
      have hCb1 : C.namesBelow (flattenR C n).next := hCb.mono hnn1
      have hsb1 : (Concept.some r C).namesBelow (flattenR C n).next :=
        fun b hb => hCb1 b hb
      have hEm : ¬ (Concept.some r C).mentions (flattenR C n).next :=
        not_mentions_of_namesBelow hsb1 (Nat.le_refl _)
      have hagD : AgreeBelow I₁
          (defineInterp I₁ (flattenR C n).next (Concept.some r C)) (flattenR C n).next :=
        agree_defineInterp I₁ _ _ (Nat.le_refl _)
      have hdef := defineInterp_def_holds I₁ (flattenR C n).next (Concept.some r C) hEm
      have hnameC1 : (Concept.name (flattenR C n).atom).namesBelow (flattenR C n).next := by
        intro b hb; simp only [Concept.mentions] at hb; subst hb; omega
      have hat₁' : ∀ t d,
          ext (defineInterp I₁ (flattenR C n).next (Concept.some r C))
            (.name (flattenR C n).atom) t d ↔
          ext (defineInterp I₁ (flattenR C n).next (Concept.some r C)) C t d := by
        intro t d
        rw [ext_agree hagD _ hnameC1 t d, ext_agree hagD C hCb1 t d]
        exact hat₁ t d
      refine ⟨defineInterp I₁ (flattenR C n).next (Concept.some r C), ?_, ?_, ?_⟩
      · exact hag₁.chain hagD hnn1
      · simp only [flattenR]
        rw [models_append]
        refine ⟨?_, ?_⟩
        · rw [models_agree hagD (flattenR_axs_below C n hCb)]
          exact hm₁
        · intro ax hax
          simp only [List.mem_singleton] at hax
          subst hax
          intro t d hat
          obtain ⟨e, hr, he⟩ := hdef.1 t d hat
          exact ⟨e, hr, (hat₁' t e).mpr he⟩
      · intro t d
        simp only [flattenR]
        exact ⟨fun hh => hdef.1 t d hh, fun hh => hdef.2 t d hh⟩

/-! ## Axiom-level normalization -/

/-- Normalize one axiom: flatten the LHS negatively, the RHS positively, and
    bridge the two atoms with one NF-EL1 axiom. -/
def normAxEL (ax : Axiom) (n : Nat) : TBox × Nat :=
  match ax with
  | .gci C D =>
      let f := flattenL C n
      let g := flattenR D f.next
      (f.axs ++ g.axs ++ [.gci (.name f.atom) (.name g.atom)], g.next)
  | .ri r s u => ([.ri r s u], n)

theorem normAxEL_le (ax : Axiom) (n : Nat) : n ≤ (normAxEL ax n).2 := by
  cases ax with
  | gci C D =>
      simp only [normAxEL]
      have h1 := flattenL_le C n
      have h2 := flattenR_le D (flattenL C n).next
      omega
  | ri r s u => simp only [normAxEL]; omega

theorem normAxEL_below (ax : Axiom) (n : Nat) (h : ax.namesBelow n) :
    (normAxEL ax n).1.namesBelow (normAxEL ax n).2 := by
  cases ax with
  | gci C D =>
      have hC : C.namesBelow n := h.1
      have hD1 : D.namesBelow (flattenL C n).next := h.2.mono (flattenL_le C n)
      have haC := flattenL_atom_lt C n hC
      have haD := flattenR_atom_lt D (flattenL C n).next hD1
      have hle2 := flattenR_le D (flattenL C n).next
      intro ax' hax'
      simp only [normAxEL] at hax' ⊢
      rcases List.mem_append.mp hax' with hax' | hax'
      · rcases List.mem_append.mp hax' with hax' | hax'
        · exact Axiom.namesBelow.mono (flattenL_axs_below C n hC ax' hax') (by omega)
        · exact flattenR_axs_below D (flattenL C n).next hD1 ax' hax'
      · simp only [List.mem_singleton] at hax'
        subst hax'
        refine ⟨fun b hb => ?_, fun b hb => ?_⟩
        · simp only [Concept.mentions] at hb; subst hb; omega
        · simp only [Concept.mentions] at hb; subst hb; omega
  | ri r s u =>
      intro ax' hax'
      simp only [normAxEL, List.mem_singleton] at hax'
      subst hax'
      trivial

theorem normAxEL_nf {ax : Axiom} (hEL : PolarityAxiom ax) (n : Nat) :
    ∀ ax' ∈ (normAxEL ax n).1, NFAxiom ax' := by
  cases ax with
  | gci C D =>
      intro ax' hax'
      simp only [normAxEL] at hax'
      rcases List.mem_append.mp hax' with hax' | hax'
      · rcases List.mem_append.mp hax' with hax' | hax'
        · exact flattenL_nf hEL.1 n ax' hax'
        · exact flattenR_nf hEL.2 (flattenL C n).next ax' hax'
      · simp only [List.mem_singleton] at hax'
        subst hax'
        exact Or.inl ⟨_, _, rfl, LhsNF.name, RhsNF.name⟩
  | ri r s u =>
      intro ax' hax'
      simp only [normAxEL, List.mem_singleton] at hax'
      subst hax'
      exact Or.inr ⟨r, s, u, rfl⟩

theorem normAxEL_sound {ax : Axiom} (hEL : PolarityAxiom ax) (I : TemporalInterp Δ) (n : Nat)
    (hm : models I (normAxEL ax n).1) : satisfies I ax := by
  cases ax with
  | gci C D =>
      simp only [normAxEL] at hm
      rw [models_append, models_append] at hm
      obtain ⟨⟨hmf, hmg⟩, hmax⟩ := hm
      intro t d hC
      have h1 := flattenL_sound hEL.1 I n hmf t d hC
      have h2 := (hmax _ (List.mem_singleton.mpr rfl)) t d h1
      exact flattenR_sound hEL.2 I (flattenL C n).next hmg t d h2
  | ri r s u =>
      simp only [normAxEL] at hm
      exact hm _ (List.mem_singleton.mpr rfl)

theorem normAxEL_complete {ax : Axiom} (hEL : PolarityAxiom ax) :
    ∀ n (I : TemporalInterp Δ), ax.namesBelow n → satisfies I ax →
      ∃ I' : TemporalInterp Δ,
        AgreeBelow I I' n ∧ models I' (normAxEL ax n).1 := by
  cases ax with
  | gci C D =>
      intro n I h hsat
      have hle1 := flattenL_le C n
      have hle2 := flattenR_le D (flattenL C n).next
      have haC := flattenL_atom_lt C n h.1
      have hD1 : D.namesBelow (flattenL C n).next := h.2.mono hle1
      have haD := flattenR_atom_lt D (flattenL C n).next hD1
      obtain ⟨I₁, hag₁, hm₁, hat₁⟩ := flattenL_complete hEL.1 n I h.1
      obtain ⟨I₂, hag₂, hm₂, hat₂⟩ := flattenR_complete hEL.2 (flattenL C n).next I₁ hD1
      have hCb1 : C.namesBelow (flattenL C n).next := h.1.mono hle1
      have hnameC1 : (Concept.name (flattenL C n).atom).namesBelow (flattenL C n).next := by
        intro b hb; simp only [Concept.mentions] at hb; subst hb; omega
      have hat₁₂ : ∀ t d, ext I₂ (.name (flattenL C n).atom) t d ↔ ext I₂ C t d := by
        intro t d
        rw [ext_agree hag₂ _ hnameC1 t d, ext_agree hag₂ C hCb1 t d]
        exact hat₁ t d
      have hsat₂ : satisfies I₂ (Axiom.gci C D) :=
        (satisfies_agree (hag₁.chain hag₂ hle1) h).mpr hsat
      refine ⟨I₂, hag₁.chain hag₂ hle1, ?_⟩
      simp only [normAxEL]
      rw [models_append, models_append]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [models_agree hag₂ (flattenL_axs_below C n h.1)]
        exact hm₁
      · exact hm₂
      · intro ax' hax'
        simp only [List.mem_singleton] at hax'
        subst hax'
        intro t d hat
        exact (hat₂ t d).mpr (hsat₂ t d ((hat₁₂ t d).mp hat))
  | ri r s u =>
      intro n I _ hsat
      refine ⟨I, AgreeBelow.rfl I n, ?_⟩
      intro ax' hax'
      simp only [normAxEL, List.mem_singleton] at hax'
      subst hax'
      exact hsat

/-! ## TBox-level normalization -/

/-- Normalize a TBox, threading the fresh-name counter through the axioms. -/
def normTBoxEL : TBox → Nat → TBox × Nat
  | [], n => ([], n)
  | ax :: rest, n =>
      let p := normAxEL ax n
      let q := normTBoxEL rest p.2
      (p.1 ++ q.1, q.2)

theorem normTBoxEL_le (T : TBox) : ∀ n, n ≤ (normTBoxEL T n).2 := by
  induction T with
  | nil => intro n; simp only [normTBoxEL]; omega
  | cons ax rest ih =>
      intro n
      simp only [normTBoxEL]
      have h1 := normAxEL_le ax n
      have h2 := ih (normAxEL ax n).2
      omega

theorem normTBoxEL_below (T : TBox) : ∀ n, T.namesBelow n →
    (normTBoxEL T n).1.namesBelow (normTBoxEL T n).2 := by
  induction T with
  | nil => intro n _ ax hax; simp only [normTBoxEL] at hax; exact absurd hax (List.not_mem_nil)
  | cons ax rest ih =>
      intro n hT ax' hax'
      have hhead : ax.namesBelow n := hT ax (List.mem_cons_self ..)
      have hrest : TBox.namesBelow rest (normAxEL ax n).2 :=
        TBox.namesBelow.mono (fun a ha => hT a (List.mem_cons.mpr (Or.inr ha))) (normAxEL_le ax n)
      have h1 := normTBoxEL_le rest (normAxEL ax n).2
      simp only [normTBoxEL] at hax' ⊢
      rcases List.mem_append.mp hax' with hax' | hax'
      · exact Axiom.namesBelow.mono (normAxEL_below ax n hhead ax' hax') (by omega)
      · exact ih (normAxEL ax n).2 hrest ax' hax'

theorem normTBoxEL_nf {T : TBox} (hEL : PolarityTBox T) :
    ∀ n, ∀ ax' ∈ (normTBoxEL T n).1, NFAxiom ax' := by
  induction T with
  | nil => intro n ax hax; simp only [normTBoxEL] at hax; exact absurd hax (List.not_mem_nil)
  | cons ax rest ih =>
      intro n ax' hax'
      simp only [normTBoxEL] at hax'
      rcases List.mem_append.mp hax' with hax' | hax'
      · exact normAxEL_nf (hEL ax (List.mem_cons_self ..)) n ax' hax'
      · exact ih (fun a ha => hEL a (List.mem_cons.mpr (Or.inr ha))) (normAxEL ax n).2 ax' hax'

theorem normTBoxEL_sound {T : TBox} (hEL : PolarityTBox T) (I : TemporalInterp Δ) :
    ∀ n, models I (normTBoxEL T n).1 → models I T := by
  induction T with
  | nil => intro n _ ax hax; exact absurd hax (List.not_mem_nil)
  | cons ax rest ih =>
      intro n hm ax' hax'
      simp only [normTBoxEL] at hm
      rw [models_append] at hm
      rcases List.mem_cons.mp hax' with hax' | hax'
      · subst hax'
        exact normAxEL_sound (hEL ax' (List.mem_cons_self ..)) I n hm.1
      · exact ih (fun a ha => hEL a (List.mem_cons.mpr (Or.inr ha))) (normAxEL ax n).2 hm.2 ax' hax'

theorem normTBoxEL_complete {T : TBox} (hEL : PolarityTBox T) :
    ∀ n (I : TemporalInterp Δ), T.namesBelow n → models I T →
      ∃ I' : TemporalInterp Δ,
        AgreeBelow I I' n ∧ models I' (normTBoxEL T n).1 := by
  induction T with
  | nil =>
      intro n I _ _
      refine ⟨I, AgreeBelow.rfl I n, ?_⟩
      intro ax hax
      simp only [normTBoxEL] at hax
      exact absurd hax (List.not_mem_nil)
  | cons ax rest ih =>
      intro n I hT hm
      have hhead : ax.namesBelow n := hT ax (List.mem_cons_self ..)
      have hrestb : TBox.namesBelow rest n := fun a ha => hT a (List.mem_cons.mpr (Or.inr ha))
      obtain ⟨I₁, hag₁, hm₁⟩ :=
        normAxEL_complete (hEL ax (List.mem_cons_self ..)) n I hhead
          (hm ax (List.mem_cons_self ..))
      have hmrest : models I₁ rest :=
        (models_agree hag₁ hrestb).mpr (fun a ha => hm a (List.mem_cons.mpr (Or.inr ha)))
      obtain ⟨I₂, hag₂, hm₂⟩ :=
        ih (fun a ha => hEL a (List.mem_cons.mpr (Or.inr ha))) (normAxEL ax n).2 I₁
          (hrestb.mono (normAxEL_le ax n)) hmrest
      refine ⟨I₂, hag₁.chain hag₂ (normAxEL_le ax n), ?_⟩
      simp only [normTBoxEL]
      rw [models_append]
      refine ⟨?_, hm₂⟩
      rw [models_agree hag₂ (normAxEL_below ax n hhead)]
      exact hm₁

/-! ## L1 — the main theorems, sorry-free -/

/-- **Lemma L1, full polarity fragment** (complete, machine-checked).

    Every polarity-respecting LTEL TBox — left sides over {⊤, names, ⊓, ∃r, ○, 𝒰}
    (hence also ◇ = ⊤𝒰·), right sides over {⊤, names, ⊓, ∃r, ○, □} — normalizes
    to a TBox in the NF shapes, as a conservative extension: equisatisfiable, and
    every model of the result is a model of the input.  The normalizer is
    `normTBoxEL` starting from `freshName T`.  The polarity precondition is
    necessary: right-side ◇/𝒰 have no sound NF (Q3), left-side □ has no NF shape. -/
theorem l1_ltel_normal_form (T : TBox) (hEL : PolarityTBox T) :
    ∃ T' : TBox,
      (∀ ax ∈ T', (∃ C D, ax = .gci C D ∧ LhsNF C ∧ RhsNF D) ∨
                   ∃ r s u, ax = .ri r s u) ∧
      (satisfiable T ↔ satisfiable T') ∧
      (∀ (Δ' : Type) (I : TemporalInterp Δ'), models I T' → models I T) := by
  refine ⟨(normTBoxEL T (freshName T)).1, ?_, ?_, ?_⟩
  · intro ax hax
    exact normTBoxEL_nf hEL (freshName T) ax hax
  · constructor
    · rintro ⟨Δ', I, hI⟩
      obtain ⟨I', _, hm⟩ :=
        normTBoxEL_complete hEL (freshName T) I (namesBelow_freshName T) hI
      exact ⟨Δ', I', hm⟩
    · rintro ⟨Δ', I, hI⟩
      exact ⟨Δ', I, normTBoxEL_sound hEL I (freshName T) hI⟩
  · intro Δ' I hI
    exact normTBoxEL_sound hEL I (freshName T) hI

/-- **Lemma L1, EL instance** — derived from the polarity theorem. -/
theorem l1_el_normal_form (T : TBox) (hEL : ELTBox T) :
    ∃ T' : TBox,
      (∀ ax ∈ T', (∃ C D, ax = .gci C D ∧ LhsNF C ∧ RhsNF D) ∨
                   ∃ r s u, ax = .ri r s u) ∧
      (satisfiable T ↔ satisfiable T') ∧
      (∀ (Δ' : Type) (I : TemporalInterp Δ'), models I T' → models I T) :=
  l1_ltel_normal_form T hEL.polarity
