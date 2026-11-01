# Contributing

[English](CONTRIBUTING.md) · [简体中文](CONTRIBUTING.zh-CN.md)

Contributions can improve a proof, clarify a mathematical definition, explain the construction, or simplify the build. A change should make its effect clear to a reader who knows the repository but has not followed its development history.

## Development environment

Use the Lean version in `lean/lean-toolchain` and the dependencies in `lean/lake-manifest.json`. Open `lean/` in an editor with Lean support. Commands below run from that directory; setup is described in [build and verification](lean/docs/Verification.md).

## Proof changes

Place changes in the relevant `CodedSorting` module and update its guide if the mathematical statement or reading order changes. Run:

```sh
python3 scripts/verify.py
```

The command builds the proofs and records theorem statements, model definitions, and axiom dependencies in `reports/`. A pull request should explain the mathematical change and include the verification command and result.

## Documentation changes

Write for a first-time reader: introduce the problem and the purpose of a construction before its details, define new terms where they appear, and link to the relevant source. Keep English and Chinese pages consistent. Documentation should stand on its own without referring to private discussions or previous editing requests.

After editing, run:

```sh
python3 scripts/check_release.py
```

This checks local links, the paper map, source excerpts, and inventory. Automatically generated pages must be updated through their generator.

## Model definitions

`ModelSnapshot.lean` prints selected statements and definitions. The verification script compares them with `docs/model-baseline.json`. For an intentional model change, explain the new definition in both model guides, update its source references in `docs/statement-correspondence.json`, and inspect the new snapshot before replacing the baseline. Then rerun verification.

## Issues

Include the file and declaration name, the relevant statement or command, and steps to reproduce the problem. For build failures, include the Lean version and the final error from `reports/build.log`.
