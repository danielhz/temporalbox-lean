# LTEL: Lean 4 formalization

Lean 4 formalization of the theoretical results of the paper *Faithful Box Embeddings for Linear Temporal EL+* (NeSy 2026): the logic LTEL, its normal form, the compilation of the temporal operators over a lasso, and the soundness and faithfulness theorems of the box embedding. The experiment code lives in a separate Python repository. Both are archived together in the DaRUS deposit [doi:10.18419/DARUS-6407](https://doi.org/10.18419/DARUS-6407). See `CITATION.cff` for how to cite.

## Layout

`LTEL.lean` is the library root; it imports the modules under `LTEL/`:

- `Syntax.lean`, `Semantics.lean`, `NormalForm.lean`, `ELNormalForm.lean` — the logic LTEL and its normal forms.
- `UntilCompilation.lean`, `Lasso.lean` — the temporal-operator compilation and the lasso (finite-horizon) machinery.
- `BoxEmbedding.lean`, `Soundness.lean`, `Faithfulness.lean`, `BoundedDimension.lean` — the box embedding and its soundness and faithfulness theorems.
- `ELBE.lean` — the machine-checked counterexample showing that ELBE is not a faithful base.
- `RigidFragment.lean`, `Tractability.lean` — the rigid reduction and the complexity commentary.
- `Conjectures.lean` — stated but unproved results; what is open is tracked here.

## Building

The toolchain is pinned in `lean-toolchain` (`leanprover/lean4:v4.30.0`) and the dependencies, Mathlib among them, in `lake-manifest.json`. Mathlib is used only where finite pigeonhole and cardinality machinery is needed; the structural proofs stay Mathlib-free.

```
lake exe cache get          # fetch Mathlib's prebuilt .olean files before the first build
lake build                  # the verification gate
lake build LTEL.Soundness   # build a single module while iterating
```

A green `lake build` with no `sorry` and no errors is what "proved" means here. Unfinished results are kept explicit: a stated theorem with a tracked `sorry`, or an entry in `Conjectures.lean`, rather than an unstated gap, so that the set of `sorry`-free theorems is the source of truth for what the paper may claim as machine-checked.

## Conventions

The default branch is `master`. Do not bump the toolchain without agreement among the authors; commit `lake-manifest.json` whenever it changes. Development tooling of individual contributors (editor or assistant configuration) is not tracked in this repository.

## License

MIT, see `LICENSE`.
