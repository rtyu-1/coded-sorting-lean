# Address-field interchange

[English](README.md) · [简体中文](README.zh-CN.md)

Exchanging two groups of address digits rearranges data. Swapping row and column indices, for example, transposes a matrix. These programs move each stored bit to the exchanged address while preserving its value.

The circuit reduces an exchange of long fields to exchanges of shorter fields, stopping when memory can handle the remaining work. The files below establish one level, the complete recursion, and the bound for arbitrary field widths.

| Reading order | Result |
| --- | --- |
| [One level](OneLevel/Exchange.lean) | Combines the circuit operations and child calls. |
| [Recursion](Recursion/ConfiguredEndpoint.lean) | Builds the complete recursive exchange program. |
| [Recursive resources](Recursion/Resources.lean) | Proves termination, workspace bounds, and the uniform cost estimate. |
| [General field widths](Fields/MachineBound.lean) | Splits arbitrary fields into widths of the form $t_0m^j$ and handles padding. |
| [Physical words and blocks](Binary/Normalized.lean) | Connects address exchange to the physical parameters used by sorting. |

[Paper guide](../README.md) · [Models](../../docs/Model.md) · [Sorting theorem explained](../../docs/SortingTheorem.md)
