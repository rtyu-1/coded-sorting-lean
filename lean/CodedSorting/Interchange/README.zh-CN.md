# 地址字段交换

[English](README.md) · [简体中文](README.zh-CN.md)

把地址中的两段数位交换，就能改变数据的排列方式。例如，交换行号与列号实现矩阵转置。这里的程序把数据送到交换后的地址，保持被移动的比特值不变。

算法用有限电路将长字段交换分成较短字段的交换，递归到内存可以处理的规模。下面的文件依次证明单层操作、完整递归，以及对一般字段宽度的复杂度上界。

| 阅读顺序 | 结果 |
| --- | --- |
| [单层交换](OneLevel/Exchange.lean) | 组合电路操作和子调用。 |
| [递归交换](Recursion/ConfiguredEndpoint.lean) | 构造完整的递归交换程序。 |
| [递归资源界](Recursion/Resources.lean) | 证明终止、工作空间界和统一的费用上界。 |
| [一般字段宽度](Fields/MachineBound.lean) | 把一般字段拆成宽度形如 $t_0m^j$ 的子字段，并处理填充。 |
| [机器字与物理块](Binary/Normalized.lean) | 把地址交换换算到排序使用的物理参数。 |

[论文导读](../README.zh-CN.md) · [模型说明](../../docs/Model.zh-CN.md) · [排序定理详解](../../docs/SortingTheorem.zh-CN.md)
