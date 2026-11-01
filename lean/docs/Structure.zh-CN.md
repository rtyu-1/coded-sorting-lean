# 源码结构

[English](Structure.md) · [简体中文](Structure.zh-CN.md)

证明有一个共用起点：固定的有限电路。从这里，一条路线实现地址交换并完成排序，另一条路线构造网络并比较编码与路由。源码按这几个数学任务组织。

## 证明目录

| 目录 | 作用 |
| --- | --- |
| [Circuit：有限电路](../CodedSorting/Circuit/README.zh-CN.md) | 证明异或电路的输入输出关系，计算节点矩阵和固定参数 |
| [Interchange：地址字段交换](../CodedSorting/Interchange/README.zh-CN.md) | 用电路递归重排数据，证明交换结果、空间和费用 |
| [Sorting：整数排序](../CodedSorting/Sorting/README.zh-CN.md) | 组合局部排序、按高位数位分组和小内存程序，得到主定理 |
| [NetworkCoding：网络编码](../CodedSorting/NetworkCoding/README.zh-CN.md) | 构造通信协议，证明消息恢复、编码速率和路由上界 |
| [Shared：共用定义](../CodedSorting/Shared/README.zh-CN.md) | 定义机器字、块存储、流操作和执行费用 |
| [Generated：有限计算证明](../CodedSorting/Generated/README.zh-CN.md) | 保存电路的具体数据，以及逐项计算的 Lean 证明 |

各目录中的 `Framework` 存放可复用的定义与证明，相邻模块将它们用于具体构造。[论文与代码对应表](../CodedSorting/README.zh-CN.md)按定理和引理编号提供入口。

## 编译和检查入口

项目位于 `lean/`，顶层文件 `CodedSorting.lean` 导入论文的主要结果。

| 文件 | 作用 |
| --- | --- |
| `Audit.lean` | 检查主定理的完整类型和公理依赖 |
| `ReviewEndpoints.lean` | 按数学主题输出定理及其使用的定义 |
| `ModelSnapshot.lean` | 输出选定的模型定义，用于比较代码修订前后的变化 |
| `scripts/verify.py` | 编译证明并运行上述检查 |

[编译与验证](Verification.zh-CN.md)给出运行步骤。下方源码统计也提供机器可读的 [JSON 版本](source-inventory.json)。

<!-- source-inventory:start -->
## 源码统计

下表统计证明目录中的 Lean 文件和行数。有限计算数据及其逐项证明单独列出。

| 类别 | 文件 | 行 |
| --- | ---: | ---: |
| 其余证明与定义 | 335 | 116,808 |
| 有限计算数据与证明 | 89 | 81,270 |
| 合计 | 424 | 198,078 |

从 `CodedSorting.lean` 入口直接或间接导入的模块共有 **401** 个，包含入口本身。

行数覆盖 `CodedSorting/**/*.lean`，包含注释和空行，不含依赖、构建产物、历史记录及顶层入口。

运行 `python3 scripts/source_inventory.py --write` 更新统计，`scripts/verify.py` 检查统计是否与源码一致。
<!-- source-inventory:end -->
