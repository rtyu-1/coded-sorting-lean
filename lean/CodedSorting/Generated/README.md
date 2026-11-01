# Finite computation proofs

[English](README.md) · [简体中文](README.zh-CN.md)

The fixed circuit contains concrete connections, register operations, and matrices. The data and proofs of their many individual computations are generated as Lean files. Lean checks these computations during the build, and the circuit modules use them in the overall construction.

The files are organized into data, register computations, and matrix equations. The [circuit guide](../Circuit/README.md) explains their mathematical role; the entries below provide the numerical details.

| Reading order | Result |
| --- | --- |
| [Circuit data](FiniteCircuit/Data.lean) | Lists the fixed circuit data. |
| [Register computation](FiniteCircuit/RegisterTrace/Replay.lean) | Proves that the register operations implement the specified circuit transformation. |
| [Matrix equations](FiniteCircuit/EndpointAlgebraChecks.lean) | Proves the matrix equations at the circuit inputs and outputs. |

[Paper guide](../README.md) · [Models](../../docs/Model.md) · [Sorting theorem explained](../../docs/SortingTheorem.md)
