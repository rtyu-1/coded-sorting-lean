# 无向多单播网络编码

[English](README.md) · [简体中文](README.zh-CN.md)

路由沿路径转发消息；网络编码还允许中间节点组合已经收到的消息。这里把有限异或电路解释成一张无向多单播网络，证明每个目的点能恢复自己的消息，并比较两种通信方式在同一张网络上的速率。

每条边的两个方向共用容量。编码速率可以趋近于 1，而矩阵给出的路径长度约束将路由速率限制在严格小于 1 的范围内。

| 阅读顺序 | 结果 |
| --- | --- |
| [主定理](Theorem32/Theorem.lean) | 在同一网络上组合编码和路由的速率结论。 |
| [网络与编码](Theorem32/Coding.lean) | 构造网络，并规定每个节点怎样发送、接收和处理消息。 |
| [有限块长编码](FiniteCodes/BinaryLinearPipeline.lean) | 证明节点只使用已收到的信息计算发送内容，且各项运算都是二元域上的线性映射。 |
| [容量界](Routing/StrictGap.lean) | 证明路由速率严格小于 1，而编码速率至多为 1。 |
| [块长](Theorem32/FiniteCode.lean) | 选择使编码速率超过路由上界的有限块长。 |

[论文导读](../README.zh-CN.md) · [模型说明](../../docs/Model.zh-CN.md) · [排序定理详解](../../docs/SortingTheorem.zh-CN.md)
