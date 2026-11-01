# Undirected multiple-unicast network coding

[English](README.md) · [简体中文](README.zh-CN.md)

Routing forwards messages along paths; network coding also allows intermediate nodes to combine received information. These modules interpret the finite XOR circuit as an undirected multiple-unicast network, prove that each destination recovers its message, and compare the two communication rates on the same graph.

Both directions of an edge share its capacity. Coding rates approach 1, while path-length constraints obtained from the circuit matrices bound routing strictly below 1.

| Reading order | Result |
| --- | --- |
| [Main theorem](Theorem32/Theorem.lean) | Combines the coding and routing rates on one network. |
| [Network and code](Theorem32/Coding.lean) | Constructs the network and specifies how each node sends, receives, and processes messages. |
| [Finite codes](FiniteCodes/BinaryLinearPipeline.lean) | Proves that nodes use only information already received and that their operations are linear over the binary field. |
| [Capacity bounds](Routing/StrictGap.lean) | Proves that routing rates are strictly below 1 and coding rates are at most 1. |
| [Block length](Theorem32/FiniteCode.lean) | Chooses a finite block length whose rate exceeds the routing bound. |

[Paper guide](../README.md) · [Models](../../docs/Model.md) · [Sorting theorem explained](../../docs/SortingTheorem.md)
