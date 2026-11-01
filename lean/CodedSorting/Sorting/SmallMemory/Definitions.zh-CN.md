# 两个块缓冲区上的执行与地址范围

当内存低于固定阈值时，算法只使用两个物理块缓冲区。要核对这一分支，需要同时查看状态、指令、执行关系和地址限制。

## 状态与一条指令

[SmallSort.lean](SmallSort.lean) 的 `TwoWordBlockLift.State` 只有 `left`、`right` 和 `disk`。前两个字段的类型都是 `Fin B → Word w`，各占 $B$ 个字；磁盘是“自然数地址 → 一个 $B$ 字块”的函数。

| 指令 | 具体操作 | I/O |
| --- | --- | ---: |
| `readLeft a` | 将磁盘块 `a` 读入左缓冲区 | 1 |
| `readRight a` | 用两个缓冲区的内容计算地址，再读入右缓冲区 | 1 |
| `writeLeft a` | 将左缓冲区整块写到地址 `a` | 1 |
| `writeRight a` | 用缓冲区计算地址，将右缓冲区整块写出 | 1 |
| `cpu f` | 用两个缓冲区的旧内容计算两个缓冲区的新内容 | 0 |

`execute` 递归执行有限指令列表；`transfers` 对同一列表逐项相加费用。`compile` 把原来只使用两个机器字的程序中的一次字读写，转换为上述整块读写：一个逻辑字放在独立物理块的第一个位置，缓冲区中第一个字承担原来的字操作。

## 执行关系为什么表示实际运行

[SmallMemorySorting.lean](SmallMemorySorting.lean) 的 `Stage` 有三种形式：按列表顺序执行的一段指令、格式转换循环和排序主体。`Executes` 的四条构造规则分别是：

1. 空程序保持状态，费用为 0。
2. 先用 `execute` 依次执行当前列表中的指令，再运行剩余阶段，费用为 `transfers body` 加后续费用。
3. 先完成格式转换循环，再运行剩余阶段，两段费用相加。
4. 先运行排序主体，再运行剩余阶段，两段费用相加。

循环继续展开到 [BlockCompress.lean](Uniform/BlockCompress.lean) 的 `LoopProgram` 和 `Executes`。每轮首先读磁盘中的停止标记，这次读取计 1；若尚未停止，就执行固定循环体，并继续下一轮。最终检查也计 1。`TwoWordBlockLift.LoopExecutes` 对核心循环采用同样的读标记、执行循环体、费用相加规则。

这些规则只由实际的状态更新和有限执行组成。归纳构造的执行证明给出从初态到末态的有限路径。

## 连续存放的输入和输出

`File hB disk xs` 展开为：对每个 $i<|xs|$，`disk (i/B) (i%B)` 等于第 $i$ 个输入字。当一个字足以表示输入位置，即 $w\ge\lceil\log_2N\rceil$ 时，小内存程序有固定五个阶段：初始化转换、输入转换、排序、重新初始化转换、输出转换。

当 $w<\lceil\log_2N\rceil$ 时，程序根据规模参数预先列出要执行的指令序列。序列执行到哪一步由程序控制维护；两个缓冲区和全部磁盘工作数据仍按本页统计。这正是论文附录 D 采用的执行位置约定。两种分支共用上述物理块操作。

## 每次访问都在分配范围内

[PublicUnrolledBlockSort.lean](PublicUnrolledBlockSort.lean) 定义 `BoundedCode L code`，要求每个阶段满足 `BoundedStage L`。继续展开后：

- 对于按列表顺序执行的一段指令，每条读写指令的地址都必须小于 $L$。地址由缓冲区计算时，要求对任意缓冲区内容都满足这个上界。
- 循环阶段同时要求停止标记地址小于 $L$，以及循环体的每条访问都满足边界。
- 排序主体分配到从 `base` 开始、长度为 $R$ 的磁盘区域，要求 `base+R≤L`，并逐层检查主体内的所有阶段都访问各自分配的区域。
- `cpu` 只更新两个缓冲区，因此其地址条件为 `True`。

顶层将 `allocation*B` 与 `smallSpaceBound c κ N` 比较。后者展开为

$$(N+13+6N^{2u})N+(2c+16)N^2,\qquad u=\max\{1,\lceil\kappa\rceil\}.$$

固定 $c,\kappa$ 后，这就是 $N$ 的固定多项式。内存位置数则恰好为 $B+B=2B\le M$。

返回[排序定理底层定义导航](../Theorem31/Definitions.zh-CN.md)。
