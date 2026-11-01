# 主排序程序与输入输出的连接

排序结论要把“输出列表有序”与“程序实际写出的内容”连起来。[AllInputPhysical.lean](AllInputPhysical.lean) 将整数表示转换、排序主体和输出转换放进同一次运行。

## 程序从哪些信息构造

`GeneralWordNormalSorting.configuration` 把顶层的 $N,M,B,w$ 原样放进 `Configuration`，并用固定构造和字长常数确定磁盘指数及内存预留系数。`parameters` 设置输入流编号、字长上界和所需数值条件。

`CommonIntegerAllInputPhysical.algorithm q p` 调用 `CommonIntegerSortingRun.policy q (core q p) q.N`。后者由程序段 `routine` 和编号间隔 `stride` 构成；`stride` 为各程序段预留互不重叠的位置编号，程序用这些编号记录执行到哪一步。输入整数的数值不参与这些表达式；同一组规模参数下使用同一个程序。

`routine` 将输入整数转换、主排序和输出取值连接起来。`initStore` 把入口程序位置编码到工作区 `top` 中。随后 `start` 设置格式转换的输入输出块数和阶段编号，并保留传入磁盘。

## 排序结果的数学表示

[File.lean](Framework/File.lean) 的 `input xs` 将每个输入整数 $x$ 变成记录 `.data x x`，分别作为排序键和所带数据。`project` 对结果记录取回键值。`output q xs` 因而是“先形成记录、按记录排序、再取回整数”的结果列表。

顶层同时要求三个条件：

1. 最终磁盘输出区每个合法位置的值，等于 `output q xs` 对应元素。
2. `output q xs` 与 `xs` 满足 `List.Perm`。
3. `output q xs` 满足 `List.Pairwise (·≤·)`。

`List.Perm` 由空表、两边同时加相同首元素、交换相邻首元素、关系的传递构成，表示元素及其重复次数保持不变。`List.Pairwise` 的递归含义是：首元素与后面每个元素满足关系，尾表继续满足同样条件；对 `≤` 即非降序。

因此这三项合起来说明：同一次执行实际写出的 $N$ 个整数，恰好是原输入的非降序排列。`output` 是描述最终内容的函数，执行入口从磁盘读取原输入。

## 执行与终止

`blocks` 展开为容纳全部输入所需的逻辑块数，即 $\lceil N/b\rceil$。顶层的步数 `blocks+1+fuel+1+blocks+1` 覆盖输入转换、主体、输出转换及阶段切换。主体需要的 `fuel` 由存在量词给出，运行规则见[完整执行的费用](../../Shared/Memory/Definitions.zh-CN.md)。

`step prog result.1=(result.1,0)` 说明末态已停止：再执行一步仍是同一状态且不产生传输。排序、停止、内存、磁盘和 I/O 上界都作用于这同一个 `result`。

## 继续阅读程序中的自定义项

构造程序的表达式会继续调用基数排序、局部列排序、地址字段交换和内存指令。阅读时可先沿这些模块的 README 理解算法，再查对应定义正文和依赖链接。它们最终使用[物理指令](../../Shared/Programs/Definitions.zh-CN.md)修改固定内存与磁盘。

返回[排序定理底层定义导航](../Theorem31/Definitions.zh-CN.md)。
