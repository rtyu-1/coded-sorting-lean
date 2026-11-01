# Build and verification

[English](Verification.md) · [简体中文](Verification.zh-CN.md)

Lean checks the proofs of the theorems. The project verification command also prints the main statements and their model definitions, compares them with the recorded declarations, and lists the logical axioms used by the proofs. Results are saved in `lean/reports/`.

## Setup and run

Install the [Lean toolchain manager](https://lean-lang.org/install/), Git, and Python 3. Download the repository, enter `lean/`, and run:

```sh
lake --version
lake exe cache get
python3 scripts/verify.py
```

`lean-toolchain` selects Lean 4.19.0, and `lake-manifest.json` pins Mathlib and its dependencies. `lake exe cache get` downloads compiled dependencies; `verify.py` then builds this project's proofs. The initial build includes substantial finite computations. Later builds reuse completed modules.

## Verification steps

1. Check the source inventory and compile the proofs with `lake build`.
2. Print the main theorem statements and selected model definitions, comparing them with `docs/model-baseline.json`.
3. Test the comparison tool's ability to detect changed theorem statements and definitions.
4. Print the definitions used by the theorems, grouped by mathematical topic.
5. Trace project definitions from the sorting theorem, check that every dependency has an entry, and compile direct checks of primitive instructions, memory counts, and complexity formulas.
6. Compare the complete public and implementation theorem types and collect the axioms used throughout their proof dependencies.

The axiom check covers both main theorems and the finite-block coding result. It accepts the three logical principles used here: `propext` identifies logically equivalent propositions, `Classical.choice` selects an object from an existence proof, and `Quot.sound` relates equivalent representatives in a quotient type.

## Reports

| File in `reports/` | Contents |
| --- | --- |
| `verification.json` | Result, compiler version, commands, and source hashes |
| `build.log` | Compiler output; inspect its end when a build fails |
| `review.md`, `review.zh-CN.md` | Lean declarations grouped by mathematical topic |
| `axioms.log` | Main theorem type comparisons and axiom dependencies |
| `model-snapshot.log` | Model definitions printed by Lean |
| `definition-check.json`, `definition-closure.json` | Definition dependencies and coverage checks |
| `definition-contracts.log` | Lean checks of primitive operations and resource formulas |

Source hashes identify the file contents checked by a report. [The sorting theorem explained](SortingTheorem.md) supports human review of the correspondence between the assumptions, conclusion, and computational model of Theorem 3.1 and the Lean statement and definitions. The [model guide](Model.md) summarizes the sorting and communication conventions.

## Individual checks

Run these commands from `lean/`:

```sh
lake build
lake env lean ReviewEndpoints.lean
lake env lean ModelSnapshot.lean
lake env lean Audit.lean
```

For documentation changes, `python3 scripts/check_release.py` checks links, the paper map, source excerpts, and inventory files. `python3 scripts/source_inventory.py` checks source counts separately.

## GitHub Actions

The [workflow](../../.github/workflows/lean.yml) runs on pushes to `main`, `public-release`, and `public-release-*`, and on pull requests targeting those branches. When it is present on the default branch, **Run workflow** on the Actions page also starts it manually.

The workflow runs documentation checks, the proof build, and theorem checks from `lean/`, then uploads `lean/reports/`. The Actions page identifies the commit, run status, and downloadable reports.

## Build resources

`lakefile.lean` sets the Lean thread stack to 32 MiB. Linux CI uses two Lean worker threads; `LEAN_NUM_THREADS=2 python3 scripts/verify.py` applies the same setting locally. After an interrupted build, resolve the reported error and rerun the command. Lake reuses completed modules.

For a standalone Linux toolchain, set `CODED_SORTING_TOOLCHAIN` to its directory and run `python3 scripts/verify.py --builder parallel --jobs 2`. This builder records module sources, imports, compiler, and options to determine when completed results can be reused. [Build tools](../scripts/README.md) lists the supporting commands.

