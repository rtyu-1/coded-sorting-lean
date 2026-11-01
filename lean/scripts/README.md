# Build tools

[English](README.md) · [简体中文](README.zh-CN.md)

`verify.py` is the complete verification entry: it builds the proofs, checks the main statements and model definitions, and saves reports. The helpers below handle documentation, source counts, and the build environment. Run all commands from `lean/`.

## Common commands

| Tool | Purpose |
| --- | --- |
| `verify.py` | Build proofs and check theorem types, model definitions, and axiom dependencies |
| `check_release.py` | Check documentation links, the paper map, source excerpts, and import completeness |
| `source_inventory.py` | Check module and line counts; `--write` updates inventory files |
| `check_model_baseline.py` | Compare definitions printed by Lean with the recorded version |
| `test_model_baseline.py` | Test whether the definition comparison detects changes |

## Standalone toolchain

These helpers run a specified Linux Lean toolchain directly. See [build and verification](../docs/Verification.md) for invocation details.

| Tool | Purpose |
| --- | --- |
| `compile_parallel_modules.py` | Limit concurrent module compilation and reuse completed results |
| `run_lean_tool.py` | Invoke the specified Lean or Lake executable |
| `restore_pinned_packages.py` | Restore dependency revisions from the Lake manifest |
| `fetch_missing_mathlib.py` | Download missing compiled Mathlib modules |

The `.lean` and `.c` files in this directory support these standalone-toolchain commands.
