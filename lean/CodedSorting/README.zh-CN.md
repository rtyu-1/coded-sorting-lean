# 论文与代码对应表

[English](README.md) · [简体中文](README.zh-CN.md)

本页提供论文（[arXiv:2610.20079](https://arxiv.org/abs/2610.20079)）中各定理、引理与 Lean 4 源码文件的对应关系。同一映射关系亦提供机器可读的 [JSON 版本](paper-map.json)。

论文的整体证明从第 5 节的[有限线性电路](Circuit/README.zh-CN.md)出发，分为两条主线：

- **通信主线**：将电路转化为无向网络并赋予矩阵标签，证明网络编码与分数路由的容量差距（[定理 3.2](NetworkCoding/Theorem32/README.zh-CN.md)）。
- **排序主线**：利用同一电路加速[外存地址字段交换](Interchange/README.zh-CN.md)，再结合局部 Columnsort 与全局基数排序，突破比较排序的 I/O 复杂度下界（[定理 3.1](Sorting/Theorem31/README.zh-CN.md)）。

## 1. 定理与引理索引

入口文件是相应证明的阅读起点，相关构造和界可能由多个模块共同给出。

### 主要结果（第 3 节）

| 论文编号 | 论文标题与核心结论 | Lean 入口文件 |
| --- | --- | --- |
| **定理 3.1** | **外存整数排序**：给出突破比较排序界的确定性外存整数排序算法，并证明其 I/O、内存与多项式磁盘空间上界。 | [Theorem.lean](Sorting/Theorem31/Theorem.lean) |
| **定理 3.2** | **无向多单播网络上的编码优势**：构造无向多单播网络，满足 $R_{\mathrm{route}}\le 1-\frac{33}{338432}<1=R_{\mathrm{code}}$。 | [Theorem.lean](NetworkCoding/Theorem32/Theorem.lean) |

### 有限线性电路与编码反例（第 5 节与附录 B）

| 论文编号 | 论文标题与核心结论 | Lean 入口文件 |
| --- | --- | --- |
| **引理 5.1** | **基础小电路的性质**：验证带有 8 维子空间标签的基础异或电路：对 $v=111$ 对数据寄存器实现 $(x,y,z)\mapsto(x,y+x,z)$，恢复 $R=439$ 个辅助寄存器的初值，并满足标签与临时复制线的代价条件。 | [ConcreteLocalProgram.lean](Circuit/Local/ConcreteLocalProgram.lean) |
| **引理 5.2** | **输入比特的置换**：在 $m=512$ 维三轮张量构造中，三份副本共享辅助寄存器，分别互换两组数据并恢复辅助初值；独立输入总数为 $W=24{,}432{,}543$。 | [TensorThreeRound.lean](Circuit/Composition/TensorThreeRound.lean) |
| **引理 5.3** | **总边长与源汇矩阵差的秩**：核算各边矩阵差的秩之和 $S=12{,}508{,}242{,}237<Wm$，并证明每个会话的源汇矩阵差满秩，为路由上界和递归节省提供依据。 | [TensorFrameCertifiedBudget.lean](Circuit/Composition/TensorFrameCertifiedBudget.lean) |
| **推论 5.4** | **递归所用的固定参数**：确立递归所需的核心不等式 $S/W<m^{1-\varepsilon}$，其中 $\varepsilon=1.5\times10^{-5}$。 | [Exponent.lean](Circuit/Parameters/Exponent.lean) |
| **引理 B.1** | **参数不等式**：用指数级数的前四项和有理数比较证明 $\varepsilon\ln m<\eta$，其中 $\eta=33/338432$，从而验证推论 5.4 的指数选择。 | [Exponent.lean](Circuit/Parameters/Exponent.lean) |

### 地址字段交换（第 6 节与附录 C）

| 论文编号 | 论文标题与核心结论 | Lean 入口文件 |
| --- | --- | --- |
| **引理 6.1** | **地址字段交换的块传输次数**：给出宽度为 $u$ 的二进制地址字段交换的 I/O 上界及内存、磁盘空间保证，适用于 $M\ge\max\{2B,C_{\rm abs}\}$。 | [Normalized.lean](Interchange/Binary/Normalized.lean) |
| **引理 6.2** | **一层编码递归**：当前缀段数可被 $W$ 整除时，将一次宽度为 $mf$ 的交换归约为 $S$ 次宽度为 $f$、数据量为 $V/W$ 的子交换，另加线性扫描开销。 | [Exchange.lean](Interchange/OneLevel/Exchange.lean) |
| **引理 6.3** | **字段宽度为 $t_0m^k$ 时的交换**：在字段宽度 $e=t_0m^k$、前缀段数可被 $W^k$ 整除时，展开递归并在短字段处停止，得到总 I/O 上界。 | [ConfiguredEndpoint.lean](Interchange/Recursion/ConfiguredEndpoint.lean) |
| **引理 C.1** | **一般字段宽度与前缀段数下的交换**：将高位数位移入前缀并补齐小段，再分解剩余字段，把递归交换界推广到任意正整数宽度 $e$ 与前缀段数 $P$。 | [MachineBound.lean](Interchange/Fields/MachineBound.lean) |

### 局部排序与全局基数排序（第 7–8 节）

| 论文编号 | 论文标题与核心结论 | Lean 入口文件 |
| --- | --- | --- |
| **命题 7.1** | **Columnsort 归约**：对 $s=2^t$、$r=s^3$、$t\ge3$ 的矩阵，将排序归约为四轮列内排序、六次地址字段交换及常数次顺序扫描，并证明排序正确性。 | [FiniteColumnsort.lean](Sorting/Local/Columnsort/FiniteColumnsort.lean) |
| **引理 7.2** | **局部排序**：通过常数层 Columnsort 递归完成 $n\le M^2$ 条记录的局部排序，保持地址交换带来的复杂度指数改进。 | [CostBound.lean](Sorting/Local/CostBound.lean) |
| **引理 8.1** | **按一个比特组划分**：利用局部排序与区间拼接，按宽度至多 $\Theta(\log M)$ 的一个比特组分桶；局部排序后的拼接只需 $O(n/B)$ 次块传输。 | [Complete.lean](Sorting/Radix/Partition/Complete.lean) |
| **命题 8.2** | **大规模输入排序**：按比特组从高到低递归划分，并对小桶调用局部排序，得到 $N\ge M^2$ 时的全局排序界。 | [SortingTrace.lean](Sorting/Radix/SortingTrace.lean) |
| **引理 8.3** | **线性次数的逐条记录访问**：通过直接基数排序或计数排序，对所有 $M\ge2B$ 给出 $O(N)$ 次 I/O 和多项式磁盘空间的算法；主定理用它处理内存低于固定阈值的情形。 | [SmallMemorySorting.lean](Sorting/SmallMemory/SmallMemorySorting.lean) |

### 缓冲模拟与参数推广（附录 A）

| 论文编号 | 论文标题与核心结论 | Lean 入口文件 |
| --- | --- | --- |
| **引理 A.1** | **带缓冲的磁带模拟**：以三块滑动窗口缓冲磁带访问，将固定条数磁带、总计 $T$ 步的 $J$ 个阶段模拟为 $O(J+T/(Bw))$ 次块传输。 | [TapeMachine.lean](Shared/Memory/TapeMachine.lean) |
| **引理 A.2** | **常数因子的块模拟**：缩小逻辑块与工作内存，并用一个物理块作中转，使正文算法能在 $M/B$ 较小（如 $M=2B$）且内存达到固定阈值时运行，只改变常数因子。 | [ControlledNormalization.lean](Shared/Programs/ControlledNormalization.lean) |
| **推论 A.3** | **推广至一般参数**：将排序界推广至全部合法参数 $2B\le M$；地址字段交换界则推广至 $M\ge\max\{2B,C_{\rm abs}\}$，保留其固定内存阈值。 | [PhysicalRate.lean](Sorting/Radix/PhysicalRate.lean) |

## 2. 论文表述与代码实现的技术细节对照

为了便于在 Lean 4 中组合各个构造，代码在参数、填充布局和中间引理的组织上采用了具体选择。下面将它们与论文逐项对照，并说明如何用于主定理。

| 涉及章节 | 论文中的数学表述 | Lean 代码中的实现方式与对应关系 |
| --- | --- | --- |
| **第 6.1 节与附录 C：后缀长度 $l$** | 引理 6.1 和引理 C.1 允许任意正整数后缀长度 $l\ge1$。 | 代码中的物理执行上界针对 $l$ 为字长 $w$ 的整数倍的数组，即每个后缀由完整机器字组成。第 7–8 节排序中的地址交换均以整条记录为单位，全部满足这一条件，因此该版本覆盖排序主定理中的所有调用。 |
| **附录 C：全零小段补齐** | 在每个原始大段 $p\in[P]$ 内，将 $R$ 个真实小段分别补齐到 $W^k$ 的整数倍 $R'$。 | 代码将合并后的全部真实小段统一补齐到递归所需的整除倍数。在借用高位数位后的参数条件下，两种方式的填充数据量均小于原来的两倍。补齐保留真实小段的相对顺序，低位交换保持各小段的前缀不变，因此删去填充后都得到所需的真实数据交换。 |
| **附录 A.3：块模拟缩放比例** | 引理 A.2 取工作内存 $\widehat M=\lfloor M/4\rfloor$、逻辑块 $\widehat B=\max\{1,\lfloor B/K\rfloor\}$，为物理块中转和控制信息留出空间。 | 代码用固定预留常数 $C$，取 $H=\lfloor M/C\rfloor$、$b=\max\{1,\lfloor B/C^2\rfloor\}$，统一容纳记录、缓冲区和控制信息。在相应的固定内存阈值以上，两种取法都只将内存与块大小缩小固定倍数，因而保持同一渐近 I/O 界；阈值以下的排序由引理 8.3 处理。 |
| **第 8.3 节：小内存磁盘空间** | 论文的紧凑布局只使用 $O(N)$ 个字的计数器和链表信息；即使每个字独占一个物理块，也只需 $O(NB)=O(N^2)$ 字磁盘空间。 | 在 $w\ge\lceil\log_2N\rceil$ 的分支，代码分配 $N+13+6\cdot2^w$ 个块槽位，再利用 $w=O(\log N)$ 将其换算为多项式字空间界 `smallSpaceBound`。这个界比论文的紧凑布局宽松，但满足定理 3.1 的多项式磁盘空间要求。 |
| **附录 A.1：多带图灵机模拟** | 引理 A.1 对固定条数的磁带和 $J$ 个阶段汇总给出 $O(J+T/(Bw))$ 次块传输界。 | [TapeMachine.lean](Shared/Memory/TapeMachine.lean) 证明单条磁带的三块窗口模拟及传输界；对固定条数磁带和各阶段求和的步骤写在论文中。排序的 Lean 证明直接构造流扫描程序，并在 [TriangularProgramBounds.lean](Circuit/Framework/TriangularProgramBounds.lean) 等模块中证明所需变换的执行和费用，从而得到递归所需的扫描开销。 |

## 相关文档导航

- **[排序定理详解](../docs/SortingTheorem.zh-CN.md)**：核对论文定理 3.1 的条件、结论和计算模型与 Lean 声明及相关定义的对应关系。
- **[模型说明](../docs/Model.zh-CN.md)**：外存模型、字长约定与执行控制状态的形式化说明。
- **[编译与验证](../docs/Verification.zh-CN.md)**：如何在本地编译 Lean 证明并运行自动检查脚本。
