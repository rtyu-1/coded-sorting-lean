# Integer sorting

[English](README.md) · [简体中文](README.zh-CN.md)

The sorting algorithm partitions integers by their leading digits and processes the groups recursively. Smaller groups use Columnsort, which alternates column sorts with rearrangements supplied by the address-interchange modules. Below a fixed memory threshold, a direct sorting algorithm uses two block buffers.

These modules combine the output, termination, space, and block-transfer proofs into Theorem 3.1.

| Reading order | Result |
| --- | --- |
| [Main theorem](Theorem31/Theorem.lean) | States the sorting result for all legal size parameters. |
| [Columnsort](Local/Columnsort/FiniteColumnsort.lean) | Proves the local column-sorting construction. |
| [Local sorting cost](Local/CostBound.lean) | Combines local sorting with address interchange. |
| [One partition level](Radix/Partition/Complete.lean) | Groups records by their leading digits. |
| [Global recursion](Radix/SortingTrace.lean) | Combines the partition levels and local calls. |
| [Small memory](SmallMemory/SmallMemorySorting.lean) | Sorts using two block buffers in memory. |

[Paper guide](../README.md) · [Models](../../docs/Model.md) · [Sorting theorem explained](../../docs/SortingTheorem.md)
