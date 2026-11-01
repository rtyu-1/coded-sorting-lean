# Coded Sorting

[English](README.md) · [简体中文](README.zh-CN.md)

本仓库提供论文 **Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting**（作者：Baochun Li、Zongpeng Li、Sirui Liu，[论文预印本](https://arxiv.org/abs/2610.20079)）的 Lean 4 形式化证明。

论文构造了一个无向多单播网络编码反例，证明网络编码的可达速率严格高于分数路由，从而推翻了 2004 年提出的多单播猜想；同时利用该构造的线性结构加速外存数据重排，突破了比较排序的输入/输出（I/O）复杂度下界，回答了 Aggarwal 和 Vitter 于 1988 年提出的公开问题。

## 方法概览

外存排序的大量块传输消耗在固定的数据位置重排上。本文通过以下三步将网络编码的通信优势转化为排序加速：

1. **有限线性电路与编码反例**：构造一个作用于多条数据流的有限异或电路。将其连线转化为无向网络边，即可实现严格高于分数路由上界的通信速率。
2. **用电路加速地址字段交换**：将数组均分为多条数据流送入该电路，利用异或混合与还原，把一次长地址字段交换归约为若干个更短字段的子交换，并使子问题处理的数据总量严格少于直接逐对交换。递归执行这一归约即可减少数据重排的块传输次数（具体计算见[方法导读](lean/docs/Idea.zh-CN.md)）。
3. **从固定重排到外存排序**：用上述快速地址字段交换实现 Columnsort 中的固定列间重排，通过常数层递归完成不超过 $M^2$ 规模的局部排序；再结合按高位分桶的基数排序，扩展至任意输入规模 $N$。

## 主要结果

**外存整数排序。** 设磁盘上存放 $N\ge2$ 个位长为 $w=\Theta(\log N)$ 的整数，内存可容纳 $M$ 个字，每次块传输移动 $B$ 个字，且 $2B\le M\le N$。论文给出一个确定性算法，使用至多 $M$ 字内存和多项式磁盘空间，在

$$O\left(\frac NB\left[1+\frac{\log N}{(\log(M/B))^{1-\varepsilon}(\log M)^\varepsilon}\right]\right),\qquad \varepsilon=1.5\times10^{-5},$$

次块传输内完成排序。当内存只能容纳少量磁盘块时改进尤为明显：例如当 $M=2B$、$N=B^2$ 时，比较排序需要 $\Theta(B\log B)$ 次 I/O，而本文算法只需 $O(B(\log B)^{1-\varepsilon})$ 次。算法对含重复值在内的所有输入均正确；模型与执行控制的完整约定见[模型说明](lean/docs/Model.zh-CN.md)。

**无向多单播网络编码。** 在所有边容量均为 $1$、双向共享容量的有限简单无向多单播网络上，上述电路构造使二元线性网络编码容量 $R_{\mathrm{code}}$ 严格高于分数路由容量 $R_{\mathrm{route}}$：

$$R_{\mathrm{route}}\le1-\frac{33}{338432}<1=R_{\mathrm{code}}.$$

本仓库使用 Lean 4 形式化验证了上述两个主要结果。读者可通过[论文与代码对应表](lean/CodedSorting/README.zh-CN.md)查找各定理与引理的代码实现。

## 开始阅读

建议先读[算法思路](lean/docs/Idea.zh-CN.md)，了解数据重排为何能加速排序，以及它与网络编码反例的联系；再读[排序定理详解](lean/docs/SortingTheorem.zh-CN.md)，核对论文排序定理的条件、结论和计算模型是否与 Lean 声明及相关定义一致。

需要查找具体证明时，可以按论文中的定理和引理编号查阅[论文与代码对应表](lean/CodedSorting/README.zh-CN.md)，也可以从[源码结构](lean/docs/Structure.zh-CN.md)按模块浏览实现。

## 编译证明

安装 [Lean 工具链管理器](https://lean-lang.org/install/)、Git 和 Python 3。下载仓库后，在仓库根目录执行：

```sh
cd lean
lake exe cache get
python3 scripts/verify.py
```

项目固定使用 **Lean 4.19.0** 和清单中的 Mathlib 版本。验证命令编译证明，检查主定理声明及其公理依赖，并将结果保存到 `lean/reports/`。安装、输出文件和 GitHub Actions 的说明见[编译与验证](lean/docs/Verification.zh-CN.md)。

## 参与和引用

贡献流程见 [贡献指南](CONTRIBUTING.zh-CN.md)，引用信息见 [CITATION.cff](CITATION.cff)。代码采用 [MIT 许可证](LICENSE)。
