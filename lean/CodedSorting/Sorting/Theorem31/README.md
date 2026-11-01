# Theorem 3.1: integer sorting

[English](README.md) · [简体中文](README.zh-CN.md)

Sorting repeatedly rearranges data so that records can be processed together in memory. The circuit reduces the total work in those rearrangements, and the recursion turns that saving into the final I/O bound. [Algorithm Overview](../../../docs/Idea.md) introduces the construction; [The sorting theorem explained](../../../docs/SortingTheorem.md) supports checking that the paper's assumptions, conclusion, and computational model match the Lean statement and its underlying definitions.

[`theorem_3_1`](Theorem.lean) constructs a deterministic sorting program for $N\ge2$, $B>0$, $2B\le M\le N$, and the word-width convention in the [model](../../../docs/Model.md). The program is chosen from these parameters and works for every input file, including duplicates.

The final file is sorted and preserves the input multiset. The same execution terminates, uses at most $M$ memory words and polynomial disk space, and has I/O count at most

$$C(c,\kappa)\frac NB\left[1+\frac{\log N}{(\log(M/B))^{1-\varepsilon}(\log M)^\varepsilon}\right],\qquad\varepsilon=3/200000.$$

The coefficient depends on the fixed construction and word-width constants; see the [constant-independence section](../../../docs/SortingTheorem.md#43-checking-the-independence-of-coefficient) of the sorting theorem guide.

## Theorem files

| File | Role |
| --- | --- |
| [Theorem.lean](Theorem.lean) | Public theorem and size assumptions |
| [Proof.lean](Proof.lean) | `NormalGuarantee`, `SmallGuarantee`, and the coefficient shared by both cases |
| [LargeMemory.lean](LargeMemory.lean) | Recursive sorting with physical memory and block parameters |
| [SmallMemory.lean](SmallMemory.lean) | Sorting below the fixed memory threshold |

`NormalGuarantee` ties the output and its sortedness to `run` and its accumulated cost `result.2`. `SmallGuarantee` uses the same input/output relation together with `Executes` and its cost. `Perm` expresses preservation of the input multiset; `Pairwise (· ≤ ·)` expresses nondecreasing order.

## Supporting proofs

Read the [finite circuit](../../Circuit/README.md), then [address interchange](../../Interchange/README.md), [local and global sorting](../README.md), and finally the files above. The [paper guide](../../README.md) lists the intermediate results in order. Model conventions, including the small-memory execution controller, are collected on the [model page](../../../docs/Model.md).

[Definition guides by module (Chinese)](Definitions.zh-CN.md) · [Coefficient dependencies (Chinese)](Constants.zh-CN.md)
