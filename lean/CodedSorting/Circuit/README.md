# Finite circuit

[English](README.md) · [简体中文](README.zh-CN.md)

Both sorting and network coding use the fixed circuit constructed here. It combines input bit streams with XOR and recovers the original values at specified outputs. A matrix at each node describes a storage order and also contributes to the routing bound on the associated network.

The modules prove the local operations, compose them into the complete circuit, and establish the fixed parameters used in the complexity analysis.

| Reading order | Result |
| --- | --- |
| [Local operation](Local/ConcreteLocalProgram.lean) | Proves the effect of the concrete XOR program. |
| [Matrix labels](Labels/FiniteInterpretation.lean) | Proves that the node matrices satisfy the circuit input and output relations. |
| [Three rounds](Composition/TensorThreeRound.lean) | Proves exchange of the original data and restoration of auxiliary values. |
| [Total edge length](Composition/TensorFrameCertifiedBudget.lean) | Assigns each connection a length equal to the rank of its endpoint-matrix difference and sums these lengths to obtain $S$ for the recursion and routing bounds. |
| [Counts](Parameters/Counts.lean) | Gives the fixed stream count $W$ and total edge length $S$. |
| [Exponent](Parameters/Exponent.lean) | Proves the strict parameter inequalities for the improved exponent. |

[Paper guide](../README.md) · [Models](../../docs/Model.md) · [Sorting theorem explained](../../docs/SortingTheorem.md)
