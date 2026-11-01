# 阅读指南

[English](README.md) · [简体中文](README.zh-CN.md)

本项目用同一个有限异或电路证明外存整数排序的复杂度上界和无向多单播网络中的编码优势。文档从算法的直觉出发，逐步连接数学陈述、Lean 定义和完整证明。

初次阅读可以从[算法思路](Idea.zh-CN.md)开始。核对论文排序定理与 Lean 声明及定义的对应关系，阅读[排序定理详解](SortingTheorem.zh-CN.md)；了解编码与路由的容量差距，阅读[网络编码定理](../CodedSorting/NetworkCoding/Theorem32/README.zh-CN.md)。阅读导读不需要先安装 Lean；运行证明检查的步骤见[编译与验证](Verification.zh-CN.md)。

| 文档 | 内容 |
| --- | --- |
| [算法思路](Idea.zh-CN.md) | 数据重排、电路如何减少处理的数据量，以及同一电路如何用于网络编码 |
| [模型说明](Model.zh-CN.md) | 输入、机器字、内存、执行控制和通信容量 |
| [排序定理详解](SortingTheorem.zh-CN.md) | 核对论文定理 3.1 的条件、结论和计算模型与 Lean 声明及相关定义的对应关系 |
| [论文与代码对应表](../CodedSorting/README.zh-CN.md) | 论文中各个编号结果的证明入口 |
| [源码结构](Structure.zh-CN.md) | 各目录承担的任务、相互关系与源码统计 |
| [编译与验证](Verification.zh-CN.md) | 本地编译、检查报告和自动验证 |

需要进一步查看具体实现时，可用[按模块查找定义的入口](../CodedSorting/Sorting/Theorem31/Definitions.zh-CN.md)定位执行、内存、磁盘和费用定义，或通过[完整定义索引](DefinitionIndex.zh-CN.md)继续追踪依赖。
