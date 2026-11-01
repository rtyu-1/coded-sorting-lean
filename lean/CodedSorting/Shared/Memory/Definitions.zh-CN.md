# 输入转换、排序执行与输出转换

输入和输出的整数连续存放，依次填入每个 $B$ 字物理块；排序主体则按较小的 $b$ 字逻辑块处理数据。每个逻辑块单独占用一个物理块的前 $b$ 个字。`CommonNormalizationController` 把两次格式转换与排序主体连接成同一条执行序列，并累计其中每次物理块读写。

## 同一磁盘上的输入区、工作区和输出区

[NormalizationController.lean](NormalizationController.lean) 将磁盘分成输入区、工作区和输出区，每区 $R=N^E$ 个物理块。`expandView`、`compactView` 和 `coreState` 分别选出当前阶段使用的区域。`installExpand`、`installCompact`、`installCore` 将更新写回原磁盘对应区域，并保留其他区域。

这些函数按地址的左右标记选择内容。例如 `installCore old new` 在工作区返回 `new a`，在输入区和输出区仍返回 `old` 的内容。因此，更新工作区时，输入区和输出区的数据保持不变。

## 输入转换的七个阶段

[PhysicalNormalizationLayout.lean](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.lean) 的 `step` 从紧凑输入取出第 $j$ 个逻辑块。它先清空 $b$ 字暂存区，再读取这个逻辑块可能跨越的两个物理输入块，从中取出所需字，最后把暂存区装入中转块并写到工作区第 $j$ 块。

七个阶段中，两次读和一次写各计 1，其余阶段计 0。计数器和当前阶段的编号分别放在 `counter : Words d w` 和 `phase : Word w`。下标 `j` 是对这些字的解码。每轮完成后，把 $j+1$ 编码回原计数器位置。

## 输出转换的八个阶段

[PhysicalNormalizationCompact.lean](PhysicalNormalizationCompact.lean) 先读取一个工作区逻辑块，提取有效的 $b$ 个字，然后依次读取、修改、写回它可能覆盖的两个输出物理块。八个阶段共计五次物理块传输。额外分配的末尾块使最后一次边界访问也有合法地址。

`extract` 按绝对字地址判断输入块内哪些字属于当前逻辑块；`patchBuffer` 按相同方法替换输出块中的目标位置，其他位置保持原值。这两项都只对已经读入的内存块进行计算。

## 顶层的 `step` 和 `run`

`stage=0` 时，顶层 `step` 运行输入转换的七步；输入完成后转入排序主体。`stage=1` 时，运行两步 [FixedPolicyNormalization](../Programs/Definitions.zh-CN.md)，完成一条逻辑指令所需的读写和内存操作。主体停止后转入输出转换。`stage=2` 时，运行输出转换的八步；完成后进入停止阶段。停止阶段返回原状态和费用 0。

因此，顶层一次 `step` 可以包含多次物理传输。它返回的费用是内部步骤费用之和。`run` 再递归累加这些费用：零步费用为 0；多一步就执行 `step`，运行剩余步数，再相加。

`fuel` 是数学上指定观察多少步的自然数。程序是否停止由当前状态中的阶段编号，以及程序根据工作内存选出的下一条指令决定。主定理给出某个有限 `fuel`，并同时证明最终 `step` 保持状态不变、费用为 0。

`initial` 只设置工作内存、缓冲区、计数器和阶段编号，并保留传入的原始磁盘。`outputWord` 最终从输出区的第 $\lfloor i/B\rfloor$ 个物理块、第 $i\bmod B$ 个字读取结果。输入转换、排序、输出转换的费用因而属于同一次执行。

返回[排序定理底层定义导航](../../Sorting/Theorem31/Definitions.zh-CN.md)。
