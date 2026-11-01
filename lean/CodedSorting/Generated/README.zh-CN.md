# 有限计算证明

[English](README.md) · [简体中文](README.zh-CN.md)

固定电路包含具体的连线、寄存器操作和矩阵。它们的数量较多，适合将数据及逐项计算的证明生成为 Lean 文件。构建项目时，Lean 检查这些计算，再由有限电路模块把它们用于整体构造。

这里的文件按数据、寄存器计算和矩阵等式组织。理解算法可以先读[有限电路导读](../Circuit/README.zh-CN.md)；需要查看具体数值时，再进入下表中的文件。

| 阅读顺序 | 结果 |
| --- | --- |
| [电路数据](FiniteCircuit/Data.lean) | 列出电路的固定数据。 |
| [寄存器计算](FiniteCircuit/RegisterTrace/Replay.lean) | 证明逐步执行寄存器操作得到规定的电路变换。 |
| [矩阵等式](FiniteCircuit/EndpointAlgebraChecks.lean) | 证明电路输入输出处的矩阵等式。 |

[论文导读](../README.zh-CN.md) · [模型说明](../../docs/Model.zh-CN.md) · [排序定理详解](../../docs/SortingTheorem.zh-CN.md)
