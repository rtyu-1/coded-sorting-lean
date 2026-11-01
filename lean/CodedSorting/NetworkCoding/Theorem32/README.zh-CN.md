# 定理 3.2：编码与路由

[English](README.md) · [简体中文](README.zh-CN.md)

网络编码允许节点把不同来源的消息组合后发送。定理 3.2 给出一张具体网络：这种组合方式能达到比沿路径转发消息更高的公共速率。它使用的异或电路与排序构造相同，联系见[方法导读](../../../docs/Idea.zh-CN.md)。

[`theorem_3_2`](Theorem.lean) 给出一张有限简单无向多单播网络，源消息相互独立、边容量均为 $1$，并且

$$R_{\mathrm{route}}\le1-\frac{33}{338432}<1=R_{\mathrm{code}}.$$

每条物理边的两个方向共用容量。一个有限块长的二元线性编码已经能达到高于 $1-33/338432$ 的速率。

## 证明文件

| 文件 | 作用 |
| --- | --- |
| [Coding.lean](Coding.lean) | 网络、源宿点对和具体编码协议 |
| [Proof.lean](Proof.lean) | 秩界、路由界和组合后的结果 |
| [FiniteCode.lean](FiniteCode.lean) | 有限块长及其达到的速率 |
| [Theorem.lean](Theorem.lean) | 完整定理 |

电路中的原始数据流对应独立消息，临时副本携带计算中使用的信息。[三轮电路证明](../../Circuit/Composition/TensorThreeRound.lean)给出原始数据的恢复，[TensorNetworkGeometry](../../Circuit/Composition/TensorNetworkGeometry.lean)确定会话及其端点。

每个会话传送 $k$ 比特时，编码让连续各批消息依次通过网络：前一批向后传递时，后一批已经进入。这种流水线安排共需 $k+D$ 轮，$D$ 由固定网络决定。速率 $k/(k+D)$ 趋近于 $1$。源点处的容量约束给出所有这些通信协议的速率上界 $1$，其中也包括二元线性编码。因此，编码容量恰好为 $1$。

将一条边两端矩阵之差的秩作为边长后，每条源宿路径都必须经过足够大的总长度。这给出同一张图上的路由上界。`strictBlock_rate_gt_gap` 证明一个有限编码的速率超过该数值上界；`paper_finite_block` 给出块长 $\lceil D(1-\eta)/\eta\rceil+1$ 的版本。

[网络模块](../README.zh-CN.md) · [模型说明](../../../docs/Model.zh-CN.md) · [论文导读](../../README.zh-CN.md)
