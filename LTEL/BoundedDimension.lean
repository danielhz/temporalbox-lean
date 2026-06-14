import Mathlib.Data.Fintype.Prod
import Mathlib.Order.Basic

/-!
# Q2: no fixed embedding dimension is faithful (the geometric core)

**Question (Q2).** Does a fixed box-embedding dimension `d`, independent of the
TBox, suffice for a faithful embedding?

The *existence*-phrased version is trivial in the ⊥-free fragment (the total
model embeds in dimension 1, just as satisfiability is trivial, cf.
`every_tbox_satisfiable`).  The informative version concerns a **single**
faithful embedding — the practical setting, where one trained embedding must
answer all (non-)entailment queries.  Such an embedding represents the canonical
model, and faithfulness *itself* supplies the exclusions: a non-entailment
`x ⋢ B` forces the point of `x` to lie **outside** the box of `B`.  No `⊥` is
needed for exclusion — entailment-completeness provides it.

**Verdict: REFUTED.**  Take `T_n = { X_i ⊑ Y_j : i ≠ j }`.  Its canonical model
has generators `e_1, …, e_n` with `e_i ∈ Y_j` iff `j ≠ i`, so each `Y_j` is the
**co-singleton** `{e_i : i ≠ j}`.  Realizing `n` co-singletons with axis-parallel
boxes in dimension `d` requires `n ≤ 2d` (this file): each excluded point must be
a strict per-axis extreme, and there are only `2d` extremes (min/max per axis).
Hence the dimension grows with `|T_n|` — no fixed `d` is faithful.

This file proves the geometric heart (`cosingleton_dim_lb`, `no_fixed_dimension`)
for an arbitrary linearly-ordered coordinate type — in particular ℝ, matching the
paper's ℝᵈ.  The reduction from `T_n`'s canonical model to the co-singleton
pattern is described above; its full mechanization (an EL canonical-model
construction) is deferred to the journal version.
-/

namespace BoundedDimension

variable {α : Type} [LinearOrder α]

/-- An axis-parallel box in `α^d`: lower and upper corner per axis. -/
structure DBox (d : Nat) (α : Type) where
  lo : Fin d → α
  hi : Fin d → α

/-- A point is in the box iff it is within `[lo, hi]` on every axis. -/
def DBox.mem {d : Nat} (b : DBox d α) (p : Fin d → α) : Prop :=
  ∀ a, b.lo a ≤ p a ∧ p a ≤ b.hi a

/-- **Co-singleton dimension lower bound.**  If `n` points and `n` axis-parallel
    boxes in `α^d` realize the co-singleton incidence — box `j` contains every
    point except `p j`, and excludes `p j` — then `n ≤ 2d`.

    Proof: each excluded `p j` lies outside box `j` on some axis `a`, so on that
    axis `p j` is a *strict* extreme (max or min) among all points (every other
    point is inside the box's interval there).  The map `j ↦ (axis, max?/min?)`
    is injective into `Fin d × Bool` (two points cannot both be the strict max,
    or both the strict min, on the same axis), so `n ≤ 2d`. -/
theorem cosingleton_dim_lb {n d : Nat}
    (p : Fin n → Fin d → α) (box : Fin n → DBox d α)
    (hin : ∀ i j, i ≠ j → (box j).mem (p i))
    (hout : ∀ j, ¬ (box j).mem (p j)) :
    n ≤ 2 * d := by
  classical
  -- For each j, an axis on which j is a strict extreme.
  have key : ∀ j, ∃ a : Fin d,
      (∀ i, i ≠ j → p i a < p j a) ∨ (∀ i, i ≠ j → p j a < p i a) := by
    intro j
    obtain ⟨a, ha⟩ := not_forall.mp (hout j)
    rw [not_and_or] at ha
    rcases ha with ha | ha
    · -- ¬ lo a ≤ p j a : p j a is a strict minimum on axis a
      refine ⟨a, Or.inr (fun i hi => ?_)⟩
      exact lt_of_lt_of_le (not_le.mp ha) ((hin i j hi a).1)
    · -- ¬ p j a ≤ hi a : p j a is a strict maximum on axis a
      refine ⟨a, Or.inl (fun i hi => ?_)⟩
      exact lt_of_le_of_lt ((hin i j hi a).2) (not_le.mp ha)
  choose A hA using key
  -- B j = true means "j is the strict maximum on axis A j".
  let B : Fin n → Bool := fun j => if (∀ i, i ≠ j → p i (A j) < p j (A j)) then true else false
  have hB_true : ∀ j, B j = true → ∀ i, i ≠ j → p i (A j) < p j (A j) := by
    intro j h
    by_contra hc
    simp only [B, if_neg hc] at h
    exact Bool.noConfusion h
  have hB_false : ∀ j, B j = false → ∀ i, i ≠ j → p j (A j) < p i (A j) := by
    intro j h i hi
    have hnotmax : ¬ (∀ i, i ≠ j → p i (A j) < p j (A j)) := by
      intro hmax; simp only [B, if_pos hmax] at h; exact Bool.noConfusion h
    rcases hA j with hmax | hmin
    · exact absurd hmax hnotmax
    · exact hmin i hi
  let f : Fin n → Fin d × Bool := fun j => (A j, B j)
  have hinj : Function.Injective f := by
    intro j k hjk
    by_contra hne
    have hkj : k ≠ j := fun h => hne h.symm
    have hjk2 : j ≠ k := hne
    have hA' : A j = A k := congrArg Prod.fst hjk
    have hB' : B j = B k := congrArg Prod.snd hjk
    cases hbj : B j with
    | true =>
        have m1 := hB_true j hbj k hkj
        have m2 := hB_true k (hB'.symm.trans hbj) j hjk2
        rw [← hA'] at m2
        exact absurd m1 (not_lt.mpr (le_of_lt m2))
    | false =>
        have m1 := hB_false j hbj k hkj
        have m2 := hB_false k (hB'.symm.trans hbj) j hjk2
        rw [← hA'] at m2
        exact absurd m1 (not_lt.mpr (le_of_lt m2))
  have hc : Fintype.card (Fin n) ≤ Fintype.card (Fin d × Bool) :=
    Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin, Fintype.card_prod, Fintype.card_bool] at hc
  omega

/-- **No fixed dimension is faithful (geometric form).**  For every `d` there is
    a co-singleton incidence (here on `2d+1` elements) not realizable by
    axis-parallel boxes in any linearly-ordered `α^d`.  Since the co-singleton
    incidence is exactly the canonical-model pattern of `T_n` (see header), no
    fixed embedding dimension faithfully captures all TBoxes. -/
theorem no_fixed_dimension :
    ¬ ∃ d : Nat, ∀ n : Nat,
        ∃ (α : Type) (_ : LinearOrder α) (p : Fin n → Fin d → α) (box : Fin n → DBox d α),
          (∀ i j, i ≠ j → (box j).mem (p i)) ∧ (∀ j, ¬ (box j).mem (p j)) := by
  rintro ⟨d, hd⟩
  obtain ⟨α, inst, p, box, hin, hout⟩ := hd (2 * d + 1)
  have := @cosingleton_dim_lb α inst (2 * d + 1) d p box hin hout
  omega

end BoundedDimension
