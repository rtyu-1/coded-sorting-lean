# Lean proof project

[English](README.md) · [简体中文](README.zh-CN.md)

This directory contains the Lean development for external-memory integer sorting and undirected multiple-unicast network coding. Starting from a finite circuit, the source constructs programs and networks and proves their correctness, complexity, and capacity bounds.

## Build

With the Lean toolchain manager and Python 3 installed, run these commands in this directory:

```sh
lake exe cache get
python3 scripts/verify.py
```

`lean-toolchain` and `lake-manifest.json` pin the compiler and dependencies. See [build and verification](docs/Verification.md) for setup, commands, and reports.

## Entry files

| File | Contents |
| --- | --- |
| [CodedSorting.lean](CodedSorting.lean) | Imports the paper's main results |
| [Theorem 3.1](CodedSorting/Sorting/Theorem31/Theorem.lean) | Sorting correctness and complexity |
| [Theorem 3.2](CodedSorting/NetworkCoding/Theorem32/Theorem.lean) | Coding and routing capacities on one network |

Open this directory in VS Code with the Lean 4 extension to inspect types and proof states at the cursor. The [reading guide](docs/README.md) introduces the mathematics; [source layout](docs/Structure.md) explains the directories.
