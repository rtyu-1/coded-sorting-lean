# 排序定理底层定义导航

了解论文定理 3.1（`theorem_3_1`）的条件、结论及其在 Lean 中的写法，请读[排序定理详解](../../../docs/SortingTheorem.zh-CN.md)。深入查看各模块的数据结构、执行规则和辅助定义，请按下表选择分册。查找具体符号及其依赖，请使用[主排序定理的定义索引](../../../docs/DefinitionIndex.zh-CN.md)。

## 1. 按模块划分的定义分册

| 专题模块 | 涉及的核心定义 | 内容说明 | 分册入口 |
| --- | --- | --- | --- |
| **机器字与地址编码** | `Covers`、`Word`、`Words` | 字长的上下界、$w$ 位无符号整数、定长字数组，以及如何用多个字表示地址 | [字与地址](../../Shared/Words/Definitions.zh-CN.md) |
| **程序配置与输入输出** | `configuration`、`parameters`、`algorithm`、`start`、`output` | 如何由规模参数 $(N,M,B,w)$ 构造确定性程序、初始化状态，以及在磁盘上存放输入和输出 | [程序和输入输出](../Execution/Definitions.zh-CN.md) |
| **外层控制器与执行阶段** | `run`、`step`、`outputWord` | 输入格式转换、排序、输出格式转换三个阶段如何衔接，以及何时停止、如何累计物理块读写次数 | [完整执行](../../Shared/Memory/Definitions.zh-CN.md) |
| **物理块指令与计费** | `Instruction`、`Policy`、`primitiveStep`、`primitiveCost` | 如何通过缓冲区用物理块模拟逻辑块，以及整块读写和内存计算如何计费 | [物理指令](../../Shared/Programs/Definitions.zh-CN.md) |
| **内存与磁盘空间核算** | `ResidentIndex`、`SourceState`、`Address` | 如何统计状态字段占用的内存字数，并限定三个磁盘区域的地址范围 | [内存与磁盘空间](../Resources/Definitions.zh-CN.md) |
| **小内存分支** | `SmallGuarantee`、`Executes`、`BoundedCode` | 内存小于固定阈值 `Mcut` 时，如何在两个块缓冲区上执行指令和循环，并限制磁盘地址范围 | [小内存分支](../SmallMemory/Definitions.zh-CN.md) |
| **全局常数与复杂度公式** | `coefficient`、`Mcut`、`factor` | 内存阈值和复杂度系数由哪些固定参数决定，以及对数改进因子的具体公式 | [常数与复杂度](Constants.zh-CN.md) |

## 2. 主排序定理的定义索引（自动生成）

[主排序定理的定义索引](../../../docs/DefinitionIndex.zh-CN.md)由脚本从 Lean 编译结果生成，从 `theorem_3_1` 的声明出发，逐层收录相关定义及其依赖。索引涉及 **186 个源码模块、2,687 项声明**，其中包含 **1,693 项定义、16,166 条项目依赖链接**。

每个条目提供声明类型、定义表达式或源码入口，并链接到所依赖的其他定义，便于按符号查阅。
