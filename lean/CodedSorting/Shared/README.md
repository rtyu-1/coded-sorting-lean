# Common definitions

[English](README.md) · [简体中文](README.zh-CN.md)

Programs represent data as machine words and move it in disk blocks. An execution tracks memory and disk contents while accumulating the transfers performed by each step. These common definitions give address exchange and sorting the same storage representation and cost measure.

| Reading order | Result |
| --- | --- |
| [Word width](Words/WordConvention.lean) | Expresses the fixed relation between word width and input size. |
| [Buffered tape access](Memory/TapeMachine.lean) | Bounds the block transfers for sequential tape access. |
| [Block execution](Memory/NormalizationController.lean) | Tracks data and control variables in memory, disk operations, and the accumulated block-transfer count. |
| [Simulation](Programs/ControlledNormalization.lean) | Relates program execution across storage layouts. |

[Paper guide](../README.md) · [Models](../../docs/Model.md) · [Sorting theorem explained](../../docs/SortingTheorem.md)
