# 共用定义

[English](README.md) · [简体中文](README.zh-CN.md)

程序通过机器字表示数据，通过磁盘块搬运数据。一次执行需要记录内存和磁盘中的内容，并累加每一步产生的块传输次数。这里给出这些共用定义，使地址交换和排序使用同一种存储与费用计算方式。

| 阅读顺序 | 结果 |
| --- | --- |
| [字长](Words/WordConvention.lean) | 表达字长与输入规模之间的固定关系。 |
| [磁带缓冲](Memory/TapeMachine.lean) | 约束顺序磁带访问所需的块传输。 |
| [块操作执行](Memory/NormalizationController.lean) | 记录内存中的数据和控制变量、磁盘操作及其累计块传输次数。 |
| [模拟](Programs/ControlledNormalization.lean) | 联系不同存储布局下的程序执行。 |

[论文导读](../README.zh-CN.md) · [模型说明](../../docs/Model.zh-CN.md) · [排序定理详解](../../docs/SortingTheorem.zh-CN.md)
