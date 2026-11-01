# Source layout

[English](Structure.md) · [简体中文](Structure.zh-CN.md)

The proof starts from a fixed finite circuit. One branch uses it for address exchange and sorting; the other constructs a network and compares coding with routing. The directories follow these mathematical tasks.

## Proof directories

| Directory | Role |
| --- | --- |
| [Circuit](../CodedSorting/Circuit/README.md) | Prove the XOR circuit's input/output relations and establish its node matrices and fixed parameters |
| [Interchange](../CodedSorting/Interchange/README.md) | Rearrange data recursively and bound space and transfer costs |
| [Sorting](../CodedSorting/Sorting/README.md) | Combine local sorting, partitioning by leading digits, and small-memory programs into the main theorem |
| [NetworkCoding](../CodedSorting/NetworkCoding/README.md) | Construct protocols and prove message recovery, coding rates, and the routing bound |
| [Shared](../CodedSorting/Shared/README.md) | Define words, block storage, stream operations, and execution costs |
| [Generated](../CodedSorting/Generated/README.md) | Store concrete circuit data and Lean proofs of individual computations |

Within a topic, `Framework` contains reusable definitions and proofs. Neighboring modules apply them to the concrete construction. The [paper-to-code guide](../CodedSorting/README.md) provides entries by theorem and lemma number.

## Build and check entries

The project lives in `lean/`. Its root file, `CodedSorting.lean`, imports the paper's main results.

| File | Role |
| --- | --- |
| `Audit.lean` | Check complete main theorem types and axiom dependencies |
| `ReviewEndpoints.lean` | Print theorems and their definitions by mathematical topic |
| `ModelSnapshot.lean` | Print selected model definitions for comparison across revisions |
| `scripts/verify.py` | Build the proofs and run these checks |

[Build and verification](Verification.md) gives the commands. The source counts below are also available as [JSON](source-inventory.json).

<!-- source-inventory:start -->
## Source inventory

The table counts Lean files and lines in the proof directory, with finite computation data and their proofs listed separately.

| Category | Files | Lines |
| --- | ---: | ---: |
| Other proofs and definitions | 335 | 116,808 |
| Finite computation data and proofs | 89 | 81,270 |
| Total | 424 | 198,078 |

`CodedSorting.lean` directly or indirectly imports **401** modules, including the entry itself.

Counts cover `CodedSorting/**/*.lean`, including comments and blank lines. Dependencies, build output, historical records, and root entry files are excluded from the line counts.

Regenerate with `python3 scripts/source_inventory.py --write`; `scripts/verify.py` checks that the inventory matches the source.
<!-- source-inventory:end -->
