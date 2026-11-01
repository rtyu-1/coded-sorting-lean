# 有限电路

[English](README.md) · [简体中文](README.zh-CN.md)

排序和网络编码都使用这里构造的固定电路。电路接收若干比特流，通过异或组合它们，再在指定输出处恢复原值。每个节点还带有一个矩阵：这些矩阵决定数据流的存储顺序，也用来估计网络中路由所需的容量。

本模块先证明局部操作，再把它们组合成完整电路，最后计算复杂度分析所需的固定参数。

| 阅读顺序 | 结果 |
| --- | --- |
| [局部操作](Local/ConcreteLocalProgram.lean) | 证明具体异或程序的作用。 |
| [矩阵标签](Labels/FiniteInterpretation.lean) | 证明各节点矩阵与电路的输入输出关系一致。 |
| [三轮组合](Composition/TensorThreeRound.lean) | 证明原始数据完成交换、辅助值恢复。 |
| [总边长](Composition/TensorFrameCertifiedBudget.lean) | 将各条连线两端矩阵差的秩作为边长，求和得到递归和路由上界所用的总边长 $S$。 |
| [计数](Parameters/Counts.lean) | 给出固定流数 $W$ 和总边长 $S$。 |
| [指数](Parameters/Exponent.lean) | 证明改进指数所需的严格参数不等式。 |

[论文导读](../README.zh-CN.md) · [模型说明](../../docs/Model.zh-CN.md) · [排序定理详解](../../docs/SortingTheorem.zh-CN.md)
