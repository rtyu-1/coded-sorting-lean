# 整数排序

[English](README.md) · [简体中文](README.zh-CN.md)

排序算法先按整数的高位数位分组，再递归处理各组。规模较小的组使用 Columnsort，它交替执行列内排序和数据重排；其中的重排由地址字段交换模块完成。内存低于固定阈值时，程序使用两个块缓冲区运行直接排序算法。

本模块把这些步骤的输出、终止、空间和块传输次数组合成定理 3.1。

| 阅读顺序 | 结果 |
| --- | --- |
| [主定理](Theorem31/Theorem.lean) | 对所有合法规模参数给出排序结论。 |
| [Columnsort](Local/Columnsort/FiniteColumnsort.lean) | 证明局部按列排序的构造。 |
| [局部排序费用](Local/CostBound.lean) | 结合局部排序和地址交换。 |
| [一层分组](Radix/Partition/Complete.lean) | 按记录的高位数位分组。 |
| [全局递归](Radix/SortingTrace.lean) | 组合各层分组和局部调用。 |
| [小内存](SmallMemory/SmallMemorySorting.lean) | 使用内存中的两个块缓冲区完成排序。 |

[论文导读](../README.zh-CN.md) · [模型说明](../../docs/Model.zh-CN.md) · [排序定理详解](../../docs/SortingTheorem.zh-CN.md)
