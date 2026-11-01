# Reading guide

[English](README.md) · [简体中文](README.zh-CN.md)

The project uses one finite XOR circuit to prove an external-memory sorting bound and a coding advantage in an undirected multiple-unicast network. These guides connect the algorithmic idea to mathematical statements, Lean definitions, and proofs.

Start with [Algorithm Overview](Idea.md). Read [The sorting theorem explained](SortingTheorem.md) to check the correspondence between the paper and the Lean statement and definitions, or the [network coding theorem](../CodedSorting/NetworkCoding/Theorem32/README.md) to understand the gap between coding and routing capacity. The guides can be read without installing Lean. To run the proof checks, follow [build and verification](Verification.md).

| Document | Contents |
| --- | --- |
| [Algorithm Overview](Idea.md) | Data rearrangement, the circuit saving, and its network interpretation |
| [Models](Model.md) | Inputs, machine words, memory, execution control, and communication capacity |
| [The sorting theorem explained](SortingTheorem.md) | Correspondence between the assumptions, conclusion, and computational model of Theorem 3.1 and the Lean statement and definitions |
| [Paper-to-code guide](../CodedSorting/README.md) | Proof entries for the numbered results |
| [Source layout](Structure.md) | Directory responsibilities, dependencies, and source counts |
| [Build and verification](Verification.md) | Local builds, reports, and automated verification |
