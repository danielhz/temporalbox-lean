/-!
# ELBE faithfulness analysis (base-method soundness, interface (iii))

ELBE (Peng et al., 2022, "Description Logic EL++ Embeddings with Intersectional
Closure", arXiv:2202.14018) is an axis-parallel **box** method: each concept `C`
is a box with center `ec(C)` and offset `eo(C)` (box `= [ec−eo, ec+eo]`), and a
relation `R` is a TransE-style translation vector `ec(R)`, so `∃R.D`'s extension
is `Box(D)` translated by `−ec(R)`.

The paper proves **no** soundness/faithfulness theorem.  Our temporal lifting
needs interface point (iii): *zero per-axiom loss ⟹ the box assignment is a
logical model*.  We settle the question: **ELBE is NOT faithful** — there are
two independent zero-loss-but-not-a-model failures, both machine-checked below.
We analyse at `margin = 0` (the most favourable case; a positive margin only
loosens each loss, so unsoundness persists).

Verdict by normal form (centers/offsets per dimension):
  * NF1 `C ⊑ D`        loss-0 ⟺ `|ec(c)−ec(d)| + eo(c) ≤ eo(d)`  = containment  → SOUND
  * NF2 `C⊓D ⊑ E`      exact box intersection, then NF1                          → SOUND
  * NF3 `C ⊑ ∃R.D`     loss-0 ⟺ `Box(C)+ec(r) ⊆ Box(D)`          = containment  → SOUND
  * NF4 `∃R.C ⊑ D`     loss-0 ⟺ `|ec(c)−ec(r)−ec(d)| ≤ eo(c)+eo(d)` = OVERLAP    → UNSOUND
  * `C ⊑ ⊥`            loss-0 ⟺ `eo(c) = 0`  = singleton box, not ∅              → UNSOUND

The NF4 loss is a non-disjointness (overlap) constraint, **not** the containment
the GCI requires; and the ⊥ loss collapses the box to a point rather than
emptying it.  Hence ELBE fails interface (iii) and inherits no temporal
faithfulness guarantee.  (Contrast BoxEL/Box²EL/TransBox, which prove soundness.)
-/

namespace ELBE

/-- A 1-D axis-parallel box: center and offset (over ℤ; offsets are ≥ 0 in the
    instances we build). -/
structure Box where
  center : Int
  offset : Int

/-- Point membership: `x ∈ [center − offset, center + offset]`. -/
def Box.mem (b : Box) (x : Int) : Prop :=
  b.center - b.offset ≤ x ∧ x ≤ b.center + b.offset

/-! ## NF1 (`C ⊑ D`): containment loss — SOUND -/

/-- ELBE NF1 zero-loss (margin 0): `Box C ⊆ Box D` as the two containment
    inequalities (`|ec(c)−ec(d)| + eo(c) ≤ eo(d)`). -/
def nf1LossZero (C D : Box) : Prop :=
  D.center - D.offset ≤ C.center - C.offset ∧ C.center + C.offset ≤ D.center + D.offset

/-- **NF1 is sound**: zero loss ⟹ every point of `C` is a point of `D`. -/
theorem nf1_sound (C D : Box) (h : nf1LossZero C D) :
    ∀ x, C.mem x → D.mem x := by
  rintro x ⟨h1, h2⟩
  obtain ⟨hc1, hc2⟩ := h
  exact ⟨by omega, by omega⟩

/-! ## NF4 (`∃R.C ⊑ D`): overlap loss — UNSOUND -/

/-- The `∃R.C` box: `Box C` translated by `−ec(r)` (ELBE's relation translation). -/
def existsR (C : Box) (cR : Int) : Box := ⟨C.center - cR, C.offset⟩

/-- ELBE NF4 zero-loss (margin 0): `|（ec(c)−ec(r)) − ec(d)| ≤ eo(c)+eo(d)` — the
    OVERLAP (non-disjointness) condition between the `∃R.C` box and `Box D`. -/
def nf4LossZero (C D : Box) (cR : Int) : Prop :=
  -(C.offset + D.offset) ≤ (existsR C cR).center - D.center ∧
  (existsR C cR).center - D.center ≤ C.offset + D.offset

/-- The NF4 model condition: every point of `∃R.C` lies in `D`. -/
def nf4Holds (C D : Box) (cR : Int) : Prop :=
  ∀ x, (existsR C cR).mem x → D.mem x

/-- **ELBE is UNSOUND for NF4.**  With `Box C = [−2,2]`, `ec(r) = 0` (so `R` is
    the identity translation and `∃R.C = Box C`), `Box D = [−1,1]`: the `∃R.C`
    box and `D` overlap (NF4 loss is 0), yet `∃R.C = [−2,2] ⊄ [−1,1] = D` — the
    point `x = 2` is in `∃R.C` but not in `D`.  Zero loss, not a model. -/
theorem nf4_unsound :
    ∃ (C D : Box) (cR : Int), nf4LossZero C D cR ∧ ¬ nf4Holds C D cR := by
  refine ⟨⟨0, 2⟩, ⟨0, 1⟩, 0, ?_, ?_⟩
  · simp only [nf4LossZero, existsR]; omega          -- ∃R.C and D overlap
  · intro h
    have hmem : (existsR ⟨0, 2⟩ 0).mem 2 := by simp only [existsR, Box.mem]; omega
    have hd := h 2 hmem                               -- ⟨0,1⟩.mem 2
    simp only [Box.mem] at hd
    omega

/-! ## `C ⊑ ⊥`: offset→0 loss — UNSOUND -/

/-- ELBE `C ⊑ ⊥` zero-loss: the offset is driven to `0`. -/
def botLossZero (C : Box) : Prop := C.offset = 0

/-- The `C ⊑ ⊥` model condition: `Box C` has empty extension. -/
def botHolds (C : Box) : Prop := ∀ x, ¬ C.mem x

/-- **ELBE is UNSOUND for `C ⊑ ⊥`.**  Zero loss forces `eo(c) = 0`, but a
    zero-offset box is a **singleton** `{ec(c)}`, not the empty set: `Box C =
    [0,0]` has loss 0 yet contains the point `0`. -/
theorem bot_unsound :
    ∃ C : Box, botLossZero C ∧ ¬ botHolds C := by
  refine ⟨⟨0, 0⟩, rfl, ?_⟩
  intro h
  have hmem : (⟨0, 0⟩ : Box).mem 0 := by simp only [Box.mem]; omega
  exact h 0 hmem

/-! ## Verdict -/

/-- **ELBE is not faithful**: it has a zero-loss NF4 non-model *and* a zero-loss
    `⊥` non-model.  It therefore fails interface (iii), so the temporal
    faithfulness theorem does not transfer to it. -/
theorem elbe_not_faithful :
    (∃ (C D : Box) (cR : Int), nf4LossZero C D cR ∧ ¬ nf4Holds C D cR) ∧
    (∃ C : Box, botLossZero C ∧ ¬ botHolds C) :=
  ⟨nf4_unsound, bot_unsound⟩

end ELBE
