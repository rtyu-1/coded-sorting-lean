# 从一条指令到一次块传输

要确认 I/O 次数的含义，需要看到指令实际怎样读写磁盘。本模块把工作内存表示成固定数量的字，把磁盘表示成“块地址到块内容”的函数。

## 最底层的五种操作

[Normalization.lean](Normalization.lean) 定义 `PhysicalState`，其中 `ram` 是 $L$ 个工作字，`buffer` 是 $B$ 个中转字，`disk` 的每个地址保存 $B$ 个字。`primitiveStep` 和 `primitiveCost` 逐项对应：

| 指令 | 状态的变化 | 块传输次数 |
| --- | --- | --- |
| `localOp f` | 将 `ram` 更新为 `f ram` | 0 |
| `fetch a` | 将 `buffer` 更新为 `disk a` | 1 |
| `copyPrefix window` | 将缓冲区前 $b$ 个字复制到指定工作内存区间 | 0 |
| `stageWrite window` | 将工作区间的 $b$ 个字复制到中转块前部，其余位置放填充值 | 0 |
| `flush a` | 将地址 `a` 的整个磁盘块替换为 `buffer` | 1 |

`Function.update disk a block` 的含义是：地址等于 `a` 时返回 `block`，其他地址返回原来的内容。这里已经明确到每个存储位置的读写。

`localOp` 的函数类型是 `Words L Word → Words L Word`，参数与结果都是这 $L$ 个字。逻辑块指令的 `read a window` 被编译成 `fetch a`、`copyPrefix window`；`write a window` 被编译成 `stageWrite window`、`flush a`。所以一个逻辑块读取或写出各对应一次物理块传输。

## 内存区间和块内复制

`Window L b` 保存起点 `base` 和条件 `base+b≤L`。`slice` 取出这个区间中的值；`load` 在区间内取新值、区间外保留旧值。`blockPrefix` 取缓冲块前 $b$ 个字，`pack` 把这 $b$ 个字放到物理块前部并填好剩余位置。所有下标范围由 `Fin` 和区间条件给出。

`executePrimitives` 按列表顺序更新状态；`primitiveListCost` 按相同顺序将每条指令的 0 或 1 相加。`compiled_step_eq`、`compiled_cost_eq` 分别证明编译前后的状态变化和块传输次数一致。

## 执行下一条指令

[ControlledNormalization.lean](ControlledNormalization.lean) 的 `Instruction` 包含 `operation` 和 `resume`。后者是更新工作内存中控制字的函数，例如将程序位置移到下一条。`Policy` 的类型为“当前工作内存 → 下一条指令或停止”。读取磁盘得到的数据可以影响下一条指令，因为它已经写入当前工作内存。

[FixedPolicyNormalization.lean](FixedPolicyNormalization.lean) 再把一条指令拆成有限个阶段。阶段 0 选取指令；读操作在这一阶段装入整个物理块并计 1。阶段 1 将读入的数据放到工作区并更新控制字，计 0。写操作先在阶段 0 准备中转块，随后在阶段 2 写出整块并计 1。当前阶段的编号本身占一个机器字。

每个阶段都从当前工作内存重新计算所需指令。读写哪个地址、操作后怎样更新控制字，都由这个固定程序和当前内存内容决定。执行中保存的全部数据及地址所占字数见[内存布局](../../Sorting/Resources/Definitions.zh-CN.md)。

返回[排序定理底层定义导航](../../Sorting/Theorem31/Definitions.zh-CN.md)。
