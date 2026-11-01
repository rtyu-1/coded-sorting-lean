# 定理 3.1：整数排序

[English](README.md) · [简体中文](README.zh-CN.md)

外存排序通过重排数据，让需要比较的整数进入内存共同处理。定理 3.1 将电路带来的重排节省用于递归排序，得到下述块传输上界。[算法思路](../../../docs/Idea.zh-CN.md)介绍数学构造；[排序定理详解](../../../docs/SortingTheorem.zh-CN.md)用于核对论文定理的条件、结论和计算模型与 Lean 声明及相关定义是否一致。

[`theorem_3_1`](Theorem.lean) 在 $N\ge2$、$B>0$、$2B\le M\le N$ 及[模型说明](../../../docs/Model.zh-CN.md)给出的字长条件下，构造确定性排序程序。程序由这些参数确定，对每个输入文件都成立，包括含重复值的输入。

最终文件有序，并保留全部输入值及其重复次数。同一次执行终止，使用至多 $M$ 字内存和多项式磁盘空间，I/O 次数至多为

$$C(c,\kappa)\frac NB\left[1+\frac{\log N}{(\log(M/B))^{1-\varepsilon}(\log M)^\varepsilon}\right],\qquad\varepsilon=3/200000.$$

系数依赖固定构造和字长常数，具体见《排序定理详解》的[常数独立性一节](../../../docs/SortingTheorem.zh-CN.md#43-核验常数-coefficient-的独立性)。

## 定理文件

| 文件 | 作用 |
| --- | --- |
| [Theorem.lean](Theorem.lean) | 主定理及规模假设 |
| [Proof.lean](Proof.lean) | `NormalGuarantee`、`SmallGuarantee`，以及两个情形共用的系数 |
| [LargeMemory.lean](LargeMemory.lean) | 按物理内存和块参数实现递归排序 |
| [SmallMemory.lean](SmallMemory.lean) | 低于固定内存阈值时的排序 |

`NormalGuarantee` 把输出及其有序性与 `run` 的执行、累计费用 `result.2` 联系起来。`SmallGuarantee` 用 `Executes` 及其费用表达同样的输入输出关系。`Perm` 表示输入值及其重复次数保持不变，`Pairwise (· ≤ ·)` 表示非降序排列。

## 支撑证明

依次阅读[有限电路](../../Circuit/README.zh-CN.md)、[地址字段交换](../../Interchange/README.zh-CN.md)、[局部与全局排序](../README.zh-CN.md)，最后回到上表的文件。[论文导读](../../README.zh-CN.md)按顺序列出中间结果。[模型页](../../../docs/Model.zh-CN.md)集中说明模型约定，包括小内存情形的执行控制。

[排序定理底层定义导航](Definitions.zh-CN.md) · [复杂度常数的依赖](Constants.zh-CN.md)
