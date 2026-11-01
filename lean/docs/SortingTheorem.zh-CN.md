# 排序定理详解

[English](SortingTheorem.md) · [简体中文](SortingTheorem.zh-CN.md)

本页对照论文定理 3.1 与 Lean 4 源码，详细说明**论文中的前提条件、算法结论以及外存计算模型在形式化代码中如何表达**。

在形式化验证中，从具体算法构造到主定理的逻辑推导由 Lean 4 内核严格检查；读者与审稿人只需核验**顶层定理的声明及其所依赖的底层定义是否准确反映了论文的条件、结论与模型**。正文从主定理 `theorem_3_1` 出发，采用自顶向下的顺序逐层展开参数约定、磁盘输入输出、单步状态转移、I/O 计费规则、内存与磁盘空间边界，以及复杂度常数的参数独立性。所有源码摘录均直接取自仓库代码，并附有分块结构说明与语法解析。

> **论文定理 3.1（外存整数排序）。** 设字长满足 $w=\Theta(\log N)$。对于任意满足 $N\ge 2$、$B>0$ 及 $2B\le M\le N$ 的整数参数，存在一个由规模参数事先确定的确定性算法，能够对磁盘上的任意 $N$ 个 $w$ 位整数完成非递减排序（保留重复值），使用至多 $M$ 个字的内存和多项式规模的磁盘空间，且整次执行的物理块传输（I/O）总次数 $Q$ 满足
>
> $$Q\le C\frac NB\left[1+\frac{\log N}{(\log(M/B))^{1-\varepsilon}(\log M)^\varepsilon}\right],\qquad \varepsilon=\frac3{200000}=1.5\times 10^{-5},$$
>
> 其中常数 $C$ 与磁盘空间的多项式次数仅依赖于固定电路构造与字长常数，与规模参数 $N, M, B, w$ 及具体输入无关。

### 核验路线图

| 论文中的条件与结论 | 对应的代码定义与核验位置 |
| --- | --- |
| **1. 参数范围与字长 $w=\Theta(\log N)$** | **第 1 节**：无符号机器字 `Word`、字长下界 `Covers` 与上界不等式 |
| **2. 程序仅由规模参数事先确定** | **第 2、3 节**：程序在输入列表给定之前由规模参数构造，状态转移函数完全确定 |
| **3. 输入与输出按块紧凑存放于磁盘** | **第 2.1、3.1 节**：物理块编号 `i/B`、块内偏移 `i%B`、`InputFile` 与 `File` |
| **4. 输出非降序且保留全部重复值** | **第 2.1、3 节**：磁盘输出同时满足排列关系 `Perm` 与有序关系 `Pairwise` |
| **5. 每次物理块读写均计入 I/O** | **第 2.2、3.2 节**：展开到底层 `step` 与 `cost`，每次整块读写计 `1` 次 I/O，内存计算计 `0` |
| **6. 内存 $\le M$ 字且磁盘为多项式空间** | **第 2.3、3.3 节**：常规分支的 `ResidentIndex`、小内存分支的双缓冲区与地址界 `BoundedCode` |
| **7. 复杂度公式一致且常数独立于规模** | **第 4 节**：展开 `factor`、`epsilon`、`coefficient` 及其显式参数列表 |

*(注：本页所有 Lean 代码块均由 `check_release.py` 脚本自动核对与仓库源码的逐字一致性。)*

---

## 1. 顶层声明与分支结构

主定理位于 [Theorem.lean](../CodedSorting/Sorting/Theorem31/Theorem.lean)，其证明直接调用 [Proof.lean](../CodedSorting/Sorting/Theorem31/Proof.lean) 中的组合定理 `complete`：

```lean
theorem theorem_3_1 (c : ℕ) (κ : ℝ) (hκ : 0≤κ) (N M B w : ℕ)
    (hN : 2≤N) (hB : 0<B) (hBM : 2*B≤M) (hMN : M≤N)
    (hw : WordConvention.Covers N w c)
    (hword : (w : ℝ)*Real.log 2≤κ*Real.log (N : ℝ)) :
    (∃ hM : GeneralWordNormalSorting.Mcut c κ≤M,
      NormalGuarantee c κ hκ N M B w hN hB hBM hMN hM hw hword) ∨
    (M<GeneralWordNormalSorting.Mcut c κ ∧
      SmallGuarantee c κ N M B w hB) :=
  GeneralWordSorting.complete
    c κ hκ N M B w hN hB hBM hMN hw hword
```

**代码结构解析：**

在 Lean 4 中，定理声明的格式为 `theorem 名称 (参数与前提列表) : 结论命题 := 证明项`。上述声明由三部分组成：

1. **输入参数与前置假设（外层冒号 `:` 之前）**：
   * **数值变量**：`(c : ℕ)` 与 `(κ : ℝ)` 为刻画字长同阶关系的两个固定常数（`ℕ` 表示自然数，`ℝ` 表示实数）；`(N M B w : ℕ)` 分别为输入整数个数 $N$、内存容量 $M$（字数）、磁盘块大小 $B$（字数）和机器字长 $w$（比特数）。
   * **前置假设（以 `h` 命名的参数）**：在依赖类型论中，前提条件同样作为参数传入。例如 `(hBM : 2*B≤M)` 表示要求调用者提供不等式 $2B \le M$ 成立的证明凭证，并将其命名为 `hBM`。同理，`hκ`、`hN`、`hB`、`hMN`、`hw`、`hword` 分别对应 $\kappa \ge 0$、$N \ge 2$、$B > 0$、$M \le N$ 以及字长 $w = \Theta(\log N)$ 的上下界条件。
2. **结论命题（外层冒号 `:` 与 `:=` 之间）**：
   结论由逻辑“或”（`∨`）连接两个分支组成，按物理内存 $M$ 是否达到固定阈值 `Mcut c κ` 划分（Lean 使用空格表示函数应用，`Mcut c κ` 即 $\mathrm{Mcut}(c, \kappa)$）：

   * **左分支（常规内存）**：存在证明凭证 `hM` 满足 $\mathrm{Mcut}(c,\kappa) \le M$，且在此条件下算法满足常规内存排序保证 `NormalGuarantee ...`。
   * **右分支（有界小内存）**：满足 $M < \mathrm{Mcut}(c,\kappa)$ 且（`∧`）算法满足小内存排序保证 `SmallGuarantee ...`。
3. **证明引用（`:=` 之后）**：
   直接调用已证明的定理 `GeneralWordSorting.complete`，并将上述全部参数与前提凭证原样传入。

### 1.1 前提条件与字长约定

**机器字类型 (`Word`)**：单个 $w$ 位整数在 [WordConvention.lean](../CodedSorting/Shared/Words/WordConvention.lean) 中定义为：
```lean
abbrev Word (w : ℕ) := Fin (2 ^ w)
```
其中 `abbrev` 定义类型别名；`Fin n` 是标准库中的有界自然数类型 $\{0, 1, \ldots, n-1\}$（每个元素由自然数值及其严格小于 $n$ 的证明对构成）。因此，`Word w` 精确表示取值在 $0, \ldots, 2^w-1$ 范围内的 $w$ 位无符号整数。

**字长上下界 (`Covers` 与 `hword`)**：为了显式表达 $w=\Theta(\log N)$，代码通过 `hw` 和 `hword` 分别约束字长的下界与上界。[WordConvention.lean](../CodedSorting/Shared/Words/WordConvention.lean) 将下界谓词 `Covers` 定义为：
```lean
def Covers (N w c : ℕ) : Prop := Nat.clog 2 N ≤ c*w
```
返回类型 `: Prop` 表示这是一个逻辑命题；`Nat.clog 2 N` 表示以 $2$ 为底的上取整对数 $\lceil\log_2 N\rceil$。因此：

* **下界 `hw`** 要求 $\lceil\log_2 N\rceil \le c w$，保证常数个 $w$ 位机器字足以编码 $[N]$ 内的元素下标及 $N$ 的多项式规模磁盘地址；
* **上界 `hword`** 要求 `(w : ℝ) * Real.log 2 ≤ κ * Real.log (N : ℝ)`（其中 `(w : ℝ)` 将自然数显式转换为实数，`Real.log` 为自然对数），即 $w \ln 2 \le \kappa \ln N$。

### 1.2 按内存阈值组合两个分支 (`complete`)

与论文第 8.4 节一致，顶层组合定理 `complete` 根据内存容量 $M$ 与固定阈值 `Mcut c κ` 的大小关系进行排中律分情况讨论，将常规内存分支与小内存分支合成为完整定理：

<details>
<summary>点击展开：组合两个分支的证明源码 <code>complete</code></summary>

```lean
theorem complete (c : ℕ) (κ : ℝ) (hκ : 0≤κ) (N M B w : ℕ)
    (hN : 2≤N) (hB : 0<B) (hBM : 2*B≤M) (hMN : M≤N)
    (hw : WordConvention.Covers N w c)
    (hword : (w : ℝ)*Real.log 2≤κ*Real.log (N : ℝ)) :
    (∃ hM : GeneralWordNormalSorting.Mcut c κ≤M,
      NormalGuarantee c κ hκ N M B w hN hB hBM hMN hM hw hword) ∨
    (M<GeneralWordNormalSorting.Mcut c κ ∧ SmallGuarantee c κ N M B w hB) := by
  by_cases hM : GeneralWordNormalSorting.Mcut c κ≤M
  · exact Or.inl ⟨hM,normal_complete c κ hκ N M B w hN hB hBM hMN hM hw hword⟩
  · exact Or.inr ⟨by omega,
      small_complete c κ N M B w hN hB hBM hMN (by omega) hw hword⟩
```

</details>

**证明步骤解析：**

`by` 关键字引导策略（tactic）证明块，仅包含三行核心逻辑：

1. **`by_cases hM : GeneralWordNormalSorting.Mcut c κ ≤ M`**：按不等式 $\mathrm{Mcut}(c,\kappa) \le M$ 是否成立划分为两个子目标（分别由行首的圆点 `·` 引导）。在第一个分支中，`hM` 代表该不等式成立的证明；在第二个分支中，`hM` 代表其否定 $\neg(\mathrm{Mcut}(c,\kappa) \le M)$ 的证明。
2. **第一个分支（当 $\mathrm{Mcut}(c,\kappa) \le M$ 成立时）**：使用 `exact Or.inl ⟨hM, normal_complete ...⟩` 选择逻辑“或”的左分支（`Or.inl`），并通过尖括号 `⟨..., ...⟩` 将阈值证明 `hM` 与常规内存定理 `normal_complete` 的结果打包返回（对应论文第 6–8.2 节及附录 A.3）。
3. **第二个分支（当 $\mathrm{Mcut}(c,\kappa) \le M$ 不成立时）**：使用 `exact Or.inr ⟨by omega, small_complete ...⟩` 选择逻辑“或”的右分支（`Or.inr`）。其中 `by omega` 调用整数线性算术求解器，由 $\neg(\mathrm{Mcut}(c,\kappa) \le M)$ 自动导出严格不等式 $M < \mathrm{Mcut}(c,\kappa)$，随后调用小内存定理 `small_complete` 完成证明（对应论文第 8.3 节引理 8.3）。

---

## 2. 常规内存分支 `NormalGuarantee`

[Proof.lean](../CodedSorting/Sorting/Theorem31/Proof.lean) 中的 `NormalGuarantee` 完整刻画了当 $M \ge \mathrm{Mcut}(c,\kappa)$ 时，外存排序算法从初始磁盘状态到停机状态的运行过程与各项保证：

<details>
<summary>点击展开：常规内存分支 <code>NormalGuarantee</code> 的完整源码</summary>

```lean
def NormalGuarantee (c : ℕ) (κ : ℝ) (hκ : 0≤κ) (N M B w : ℕ)
    (hN : 2≤N) (hB : 0<B) (hBM : 2*B≤M) (hMN : M≤N)
    (hM : GeneralWordNormalSorting.Mcut c κ≤M) (hw : WordConvention.Covers N w c)
    (hword : (w : ℝ)*Real.log 2≤κ*Real.log (N : ℝ)) : Prop :=
  let q := GeneralWordNormalSorting.configuration c κ N M B w hN hB hBM hMN hM hw
  let p := GeneralWordNormalSorting.parameters c κ hκ N M B w hN hB hBM hMN hM hw hword
  ∀ (store : CommonLeafProgram.Store q)
    (disk : CommonNormalizationController.Disk (q.N^q.exponent) q.B q.w)
    (xs : List (Word w)), xs.length=N → CommonIntegerPhysical.InputFile q disk xs →
    ∃ fuel,
      let prog := program q (CommonIntegerAllInputPhysical.algorithm q p)
      let s := CommonIntegerAllInputPhysical.start q p store disk
      let blocks := CommonIntegerPhysical.blocks q q.N
      let result := CommonNormalizationController.run prog (blocks+1+fuel+1+blocks+1) s
      (∀ i : Fin (CommonIntegerFile.output q xs).length,
        CommonNormalizationController.outputWord prog result.1 i.val=(CommonIntegerFile.output q xs).get i) ∧
      (CommonIntegerFile.output q xs).Perm xs ∧
      (CommonIntegerFile.output q xs).Pairwise (·≤·) ∧
      CommonNormalizationController.step prog result.1=(result.1,0) ∧
      Fintype.card (ResidentIndex q)≤M ∧
      Fintype.card (CommonNormalizationController.Address (q.N^q.exponent))≤
        N^(GeneralWordNormalSorting.exponent κ+2) ∧
      Fintype.card (CommonNormalizationController.Address (q.N^q.exponent))*B≤
        N^(GeneralWordNormalSorting.exponent κ+3) ∧
      (result.2 : ℝ)≤coefficient c κ*((N : ℝ)/B)*factor N M B
```

</details>

**`NormalGuarantee` 的分块逻辑解析：**

上述命题定义按执行顺序分为四个逻辑层次：

1. **打包机器配置与算法参数（前两行 `let`）**：
   `let q := ...` 与 `let p := ...` 定义局部常量，将外层传入的规模参数 $(N, M, B, w)$ 及前提条件封装为机器配置结构体 `q` 和算法参数结构体 `p`。

2. **对任意合法输入的普适性（全称量词 `∀` 与蕴含箭头 `→`）**：
   `∀ (store : ...) (disk : ...) (xs : List (Word w)), xs.length = N → InputFile q disk xs →` 表示：对于任意初始内存工作区 `store`、任意初始磁盘内容 `disk` 以及任意由 $w$ 位整数组成的列表 `xs`，**若**列表长度恰好为 $N$，并且该列表已按规定格式存放在初始磁盘 `disk` 的输入区中（`InputFile q disk xs`），则以下运行结论成立。

3. **构造确定性程序并执行有限步（存在量词 `∃ fuel` 与 `run`）**：
   存在有限自然数步数 `fuel`，使得：

   * 由配置 `q` 和参数 `p` 构造出排序程序 `prog := program q (algorithm q p)`（注意：`prog` 的定义中完全不出现输入列表 `xs`，从语法上保证了程序仅由规模参数事先确定）；
   * 由 `store` 和 `disk` 组装机器初始状态 `s`，并计算输入输出块格式转换所需的逻辑块数 `blocks`（即 $\lceil N/b \rceil$）；
   * 调用控制器执行函数 `run prog (blocks+1+fuel+1+blocks+1) s`，依次运行输入转换（`blocks` 步）、阶段切换（`1` 步）、主排序算法（`fuel` 步）、阶段切换（`1` 步）、输出转换（`blocks` 步）及停机切换（`1` 步）。`run` 返回二元组 `result`，其中第 1 项 **`result.1`** 为最终机器状态，第 2 项 **`result.2`** 为整次执行累计的物理块传输（I/O）次数。
4. **八项合取结论（以逻辑“且” `∧` 连接的八项结论）**：
   前 4 项验证最终状态 `result.1` 的磁盘输出正确性与正常停机；后 4 项验证内存字数、磁盘块数、磁盘字数以及累计 I/O 次数 `result.2` 满足定理上界。

下面我们分三步逐一展开并核验这八项结论背后引用的底层定义。

### 2.1 核验一：磁盘输入输出格式与排序正确性

**1. 磁盘区域划分与输入文件 (`InputFile`)**。

令 $R = N^E$，其中 $E = \mathtt{exponent}(\kappa)$ 为仅依赖于字长常数 $\kappa$ 的固定指数。代码使用带标签的不交并类型（Sum Type，记为 `α ⊕ β`，通过左构造器 `.inl` 与右构造器 `.inr` 区分元素来源）将磁盘块地址空间定义为 `Address R = Fin R ⊕ (Fin R ⊕ Fin R)`。由此，`.inl a`、`.inr (.inl a)` 与 `.inr (.inr a)` 分别标识**输入区、工作区、输出区**三个互不重叠的磁盘区域，每个区域包含 $R$ 个物理块，每个物理块包含 $B$ 个 $w$ 位字。

在 [PhysicalHalted.lean](../CodedSorting/Sorting/Execution/Framework/PhysicalHalted.lean) 中，`inputWord` 与 `InputFile` 规定了输入列表 `xs` 在磁盘上的物理存储位置：

```lean
def inputWord (q : Configuration)
    (disk : CommonNormalizationController.Disk (q.N^q.exponent) q.B q.w) (i : ℕ) : Word q.w :=
  if h : i/q.B<q.N^q.exponent then
    disk (.inl ⟨i/q.B,h⟩) ⟨i%q.B,Nat.mod_lt _ q.block_pos⟩
  else 0

def InputFile (q : Configuration)
    (disk : CommonNormalizationController.Disk (q.N^q.exponent) q.B q.w)
    (xs : List (Word q.w)) : Prop := ∀ i : Fin xs.length,inputWord q disk i.val=xs.get i
```

**代码解析：**

* 在 `inputWord` 中，自然数整除 `i / q.B` 计算第 $i$ 个整数所在的物理块编号，取模 `i % q.B` 计算其在块内的字偏移；`disk (.inl ⟨i/q.B, h⟩) ⟨i%q.B, ...⟩` 即读取磁盘**输入区**（`.inl`）第 $\lfloor i/B \rfloor$ 块的第 $i \bmod B$ 个字（尖括号 `⟨数值, 证明⟩` 用于构造有界下标 `Fin`）。
* 在 `InputFile` 中，全称量词 `∀ i : Fin xs.length` 要求对于列表 `xs` 的每一个合法下标 `i`，磁盘输入区对应位置上的字 `inputWord q disk i.val` 均等于列表元素 `xs.get i`。
* 输出读取函数 `outputWord` 采用完全相同的紧凑寻址方式（块号 `y / B`、块内偏移 `y % B`），从最终状态的磁盘**输出区**（`.inr (.inr ...)`）读取结果。

<details>
<summary>点击展开：定长字数组 <code>Words</code>、磁盘状态 <code>State</code> 与输出读取 <code>outputWord</code> 源码</summary>

在 Lean 中，固定长度数组通常表示为从有界下标集到元素类型的函数：下方 `Words count w` 定义为函数类型 `Fin count → Word w`（输入下标 $0 \ldots \text{count}-1$，返回对应的 $w$ 位字）；同理，`Disk R B w` 定义为从块地址 `Address R` 到物理块 `Words B w` 的映射。`structure ... where` 用于声明包含命名字段的记录类型（结构体）。

[CodedSorting/Shared/Words/WordConvention.lean](../CodedSorting/Shared/Words/WordConvention.lean)

```lean
abbrev Words (count w : ℕ) := Fin count → Word w
```

[CodedSorting/Shared/Memory/NormalizationController.lean](../CodedSorting/Shared/Memory/NormalizationController.lean)

```lean
abbrev Address (R : ℕ) := Fin R ⊕ (Fin R ⊕ Fin R)
abbrev Disk (R B w : ℕ) := Address R → Words B w

structure Program (L R B b d w : ℕ) where
  positive_region : 0 < R
  positive_block : 0 < B
  block_ratio : b ≤ B
  counter_capacity : R  <  (2^w)^d
  phase_capacity : 8 ≤ 2^w
  padding : Word w
  policy : ControlledNormalization.Policy L b R (Word w)

structure State (L R B b d w : ℕ) where
  ram : Words L w
  buffer : Words B w
  scratch : Words b w
  counter : Words d w
  inputCount : Words d w
  outputCount : Words d w
  phase : Word w
  stage : Word w
  disk : Disk R B w
```

[CodedSorting/Shared/Memory/NormalizationController.lean](../CodedSorting/Shared/Memory/NormalizationController.lean)

```lean
def outputWord (p : Program L R B b d w) (s : State L R B b d w) :=
  PhysicalNormalizationCompact.targetWord (outputProgram p s) (compactView s.disk)
```

[CodedSorting/Shared/Memory/PhysicalNormalizationCompact.lean](../CodedSorting/Shared/Memory/PhysicalNormalizationCompact.lean)

```lean
def targetWord (p : Program R B b d w) (disk : Disk R B w) : BlockReflection.Disk (Word w) :=
  fun y => disk (.inr (index p (y/B))) ⟨y%B,Nat.mod_lt _ p.positive_block⟩
```

</details>

**2. 排序正确性与不动点停机条件的核验**。

在 `NormalGuarantee` 中，前四项合取结论围绕目标列表 `CommonIntegerFile.output q xs`（下表简记为 `out`）给出了完整的正确性与停机保证：

| 代码中的结论 | 形式化含义与核验作用 |
| --- | --- |
| `∀ i : Fin out.length, outputWord prog result.1 i.val = out.get i` | **结果真实写回磁盘**：最终状态 `result.1` 的磁盘输出区前 `out.length` 个位置，逐字存放着列表 `out` 的全部元素。 |
| `out.Perm xs` | **元素守恒且保留重复值**：标准库谓词 `List.Perm` 表示 `out` 是输入列表 `xs` 的一个排列。这保证了输出长度仍为 $N$，且每个整数值出现的重数与输入完全相同。 |
| `out.Pairwise (·≤·)` | **非递减有序**：标准库谓词 `List.Pairwise R` 要求列表中任意排在前面的元素 $x$ 与排在后面的元素 $y$ 均满足关系 $R(x,y)$。此处 `(·≤·)` 为二元比较关系 $\le$ 的简写，表示输出序列单调非递减。 |
| `step prog result.1 = (result.1, 0)` | **正常停机（到达状态机不动点）**：从最终状态 `result.1` 再单步执行一次转移函数 `step`，机器状态保持 `result.1` 不变，且产生的 I/O 费用为 `0`。在确定性状态机中，此后无论再延续多少步，磁盘输出与累计 I/O 均不再发生变化。控制器走完三个阶段后进入的 `stage = 3` 静止分支满足这个条件。 |

**3. 程序的确定性与初始状态构造**。

展开下方源码可核实：机器配置 `configuration` 直接记录外层参数 $N, M, B, w$；基本命令类型 `Command` 仅包含内存局部操作 `.localOp`、逻辑块读 `.read` 与逻辑块写 `.write`；控制策略 `Policy` 是从当前工作内存 `Words L Word` 到下一条指令 `Option (Instruction ...)` 的纯函数（返回 `none` 表示主算法结束）；启动函数 `start` 则将原始输入磁盘 `disk` 原封不动地装入控制器初态 `initial` 中。

<details>
<summary>点击展开：机器配置 <code>configuration</code>、指令类型 <code>Command</code> 与初态初始化 <code>start</code> 源码</summary>

[CodedSorting/Sorting/Theorem31/LargeMemory.lean](../CodedSorting/Sorting/Theorem31/LargeMemory.lean)

```lean
def configuration (c : ℕ) (κ : ℝ) (N M B w : ℕ)
    (hN : 2≤N) (hB : 0<B) (hBM : 2*B≤M) (hMN : M≤N)
    (hM : Mcut c κ≤M) (hw : WordConvention.Covers N w c) : Configuration where
  inventory := inventory
  N := N
  M := M
  B := B
  w := w
  c := c
  exponent := exponent κ
  input_large := hN
  memory_input := hMN
  block_pos := hB
  block_memory := hBM
  exponent_pos := (by omega : 1≤17).trans
    (CodedSorting.Construction.Sorting.CommonIntegerAllInputCapacity.exponent_ge17 (wordFactor κ))
  word_convention := hw
  memory_large := hM
```

[CodedSorting/Shared/Programs/Normalization.lean](../CodedSorting/Shared/Programs/Normalization.lean)

```lean
inductive Command (L b D : ℕ) (Word : Type*)
  | localOp (f : Words L Word → Words L Word)
  | read (address : Fin D) (window : Window L b)
  | write (address : Fin D) (window : Window L b)
```

[CodedSorting/Shared/Programs/ControlledNormalization.lean](../CodedSorting/Shared/Programs/ControlledNormalization.lean)

```lean
structure Instruction (L b D : ℕ) (Word : Type*) where
  operation : Command L b D Word
  resume : Words L Word → Words L Word

abbrev Policy (L b D : ℕ) (Word : Type*) :=
  Words L Word → Option (Instruction L b D Word)
```

[CodedSorting/Sorting/Resources/Framework/NormalizationFrames.lean](../CodedSorting/Sorting/Resources/Framework/NormalizationFrames.lean)

```lean
abbrev SourcePolicy (q : Configuration) :=
  ControlledNormalization.Policy q.ramWords q.block (q.N^q.exponent) (Word q.w)
```

[CodedSorting/Sorting/Resources/Framework/NormalizationFrames.lean](../CodedSorting/Sorting/Resources/Framework/NormalizationFrames.lean)

```lean
def program (q : Configuration) (policy : SourcePolicy q) :
    CommonNormalizationController.Program q.ramWords (q.N^q.exponent)
      q.B q.block q.digits q.w where
  positive_region := pow_pos (by have := q.input_large; omega) _
  positive_block := q.block_pos
  block_ratio := Normalization.logical_block_le_physical q.B _ q.block_pos
  counter_capacity := Nat.lt_of_succ_le
    (WordConvention.polynomial_capacity q.N q.w q.c q.exponent q.input_large q.word_convention)
  phase_capacity := by
    have h := Nat.pow_le_pow_right (by decide : 0 < 2) q.word_width
    norm_num at h
    exact h
  padding := 0
  policy := policy
```

[CodedSorting/Sorting/Execution/AllInputPhysical.lean](../CodedSorting/Sorting/Execution/AllInputPhysical.lean)

```lean
def algorithm (q : Configuration) (p : Parameters q) : SourcePolicy q :=
  CodedSorting.Construction.Sorting.CommonIntegerSortingRun.policy q (core q p) q.N le_rfl

def start (q : Configuration) (p : Parameters q) (store : Store q)
    (disk : CommonNormalizationController.Disk (q.N^q.exponent) q.B q.w) : MachineState q :=
  CommonIntegerPhysical.start q (algorithm q p)
    (CodedSorting.Construction.Sorting.CommonIntegerSortingRun.initStore q (core q p) q.N le_rfl store) q.N
    (CommonIntegerCapacity.blocks_lt q q.N le_rfl (by have:=CodedSorting.Construction.Sorting.CommonIntegerAllInputCapacity.exponent_ge17 (wordFactor p.kappa);have:=p.exponent;omega)) disk
```

[CodedSorting/Sorting/Execution/Framework/PhysicalHalted.lean](../CodedSorting/Sorting/Execution/Framework/PhysicalHalted.lean)

```lean
def start (q : Configuration) (policy : SourcePolicy q) (store : Store q)
    (n : ℕ) (hn : blocks q n<q.N^q.exponent)
    (disk : CommonNormalizationController.Disk (q.N^q.exponent) q.B q.w) : MachineState q :=
  initialState q policy store ⟨blocks q n,by omega⟩ ⟨blocks q n,hn⟩ disk
```

[CodedSorting/Sorting/Resources/Framework/NormalizationFrames.lean](../CodedSorting/Sorting/Resources/Framework/NormalizationFrames.lean)

```lean
def initialState (q : Configuration) (policy : SourcePolicy q)
    (s : SourceState q.inventory q.height q.block q.digits q.w)
    (nIn : Fin (q.N^q.exponent+1)) (nOut : Fin (q.N^q.exponent))
    (disk : CommonNormalizationController.Disk (q.N^q.exponent) q.B q.w) : MachineState q :=
  CommonNormalizationController.initial (program q policy) (pack s)
    (WordConvention.encode q.N q.w q.c q.exponent q.input_large q.word_convention nIn)
    (WordConvention.encode q.N q.w q.c q.exponent q.input_large q.word_convention nOut.castSucc)
    disk
```

[CodedSorting/Shared/Memory/NormalizationController.lean](../CodedSorting/Shared/Memory/NormalizationController.lean)

```lean
def initial (p : Program L R B b d w) (ram : Words L w)
    (inputCount outputCount : Words d w) (disk : Disk R B w) : State L R B b d w :=
  ⟨ram,fun _=>p.padding,fun _=>p.padding,PhysicalNormalizationLayout.counterCode d w 0,
    inputCount,outputCount,code p 0,code p 0,disk⟩
```

</details>

### 2.2 核验二：单步执行与物理 I/O 计费

为了确认代码中的 I/O 计数器 `result.2` 忠实统计了每一次物理块读写，我们查看 [NormalizationController.lean](../CodedSorting/Shared/Memory/NormalizationController.lean) 中的多步执行函数 `run`：

```lean
def run (p : Program L R B b d w) : ℕ → State L R B b d w → State L R B b d w × ℕ
  | 0,s => (s,0)
  | fuel+1,s =>
      let first := step p s
      let rest := run p fuel first.1
      (rest.1,first.2+rest.2)
```

**代码解析：**

返回值类型 `State ... × ℕ` 表示由“机器状态”与“物理 I/O 次数”组成的二元组。函数通过模式匹配对步数进行递归：当步数为 `0` 时，返回原状态 `s` 与费用 `0`；当步数为 `fuel + 1` 时，先调用单步函数 `step p s` 得到第一步后的状态 `first.1` 与第一步的费用 `first.2`，再从 `first.1` 继续执行剩余 `fuel` 步得到 `rest`，最终返回状态 `rest.1` 并将本步费用与后续费用累加为 `first.2 + rest.2`。

**三个运行阶段与底层计费规则：**

依照论文附录 A.3（常数因子的块模拟），算法内部使用逻辑块大小 $b \le B$，并在物理内存中设置一个大小为 $B$ 字的物理块中转缓冲区 `buffer`。外层控制器的 `step` 函数根据阶段寄存器 `s.stage.val` 的取值依次调度三个阶段：

1. **阶段 `stage = 0`（输入块格式转换）**：若块计数器 `counter < inputSize`，则调用 `PhysicalNormalizationLayout.run ... 7` 执行 7 个内部微步骤——依次从输入区读取两个相邻物理块到 `buffer`（各计 `1` 次 I/O，共 `2` 次读），提取 $b$ 个有效字组装成一个逻辑块并写入工作区（计 `1` 次写 I/O），处理每个逻辑块合计产生 **3 次物理 I/O**。全部 $\lceil N/b \rceil$ 个逻辑块转换完毕后，将 `stage` 切换为 `1`（切换本身计 `0` 次 I/O）。
2. **阶段 `stage = 1`（主排序算法）**：若控制策略返回 `none`，表示排序完成，将 `stage` 切换为 `2`；否则调用 `FixedPolicyNormalization.run ... 2` 执行主算法的单条指令（含 2 个内部相位）：
   * **局部计算 `.localOp f`**：仅在内存中计算 `i.resume (f s.data.ram)`，不访问 `disk`，返回费用 **`0`**；
   * **读取块 `.read address window`**：相位 0 将工作区物理块 `s.data.disk address` 整块读入中转缓冲区 `buffer`，返回费用 **`1`**；相位 1 将 `buffer` 的前 $b$ 个字（`blockPrefix`）复制到工作内存 `ram` 的指定窗口 `window` 内，返回费用 **`0`**；
   * **写入块 `.write address window`**：相位 0 从工作内存 `ram` 的窗口 `window` 取出 $b$ 个字（`slice`）并用填充值打包成完整物理块 `buffer`（`pack`），返回费用 **`0`**；相位 2 调用 `Function.update s.data.disk address s.data.buffer` 将 `buffer` 整块写入工作区磁盘，返回费用 **`1`**。
3. **阶段 `stage = 2`（输出块格式转换）**：调用 `PhysicalNormalizationCompact.run ... 8` 执行 8 个内部微步骤——从工作区读出第 $j$ 个逻辑块（`1` 次读 I/O），再对输出区对应的两个相邻物理块分别执行“读入 `buffer` $\to$ 修改对应区间（`patchBuffer`）$\to$ 整块写回磁盘”（各需 `1` 读 `1` 写，共 `4` 次 I/O），每个逻辑块合计产生 **5 次物理 I/O**。全部转换完毕后，将 `stage` 切换为 `3`。
4. **阶段 `stage = 3`（停机分支 `| _ => (s, 0)`）**：直接返回 `(s, 0)`，状态与费用均不再改变。

展开下方源码，可直接核对上述每一个分支的真实状态更新与返回值（记录更新语法 `{s with 字段 := 新值}` 表示复制结构体 `s` 并仅修改指定字段）：

<details>
<summary>点击展开：外层控制器 <code>step</code> 与三个阶段的视图切换源码</summary>

[CodedSorting/Shared/Memory/NormalizationController.lean](../CodedSorting/Shared/Memory/NormalizationController.lean)

```lean
def code (p : Program L R B b d w) (k : Fin 8) : Word w :=
  ⟨k.val,lt_of_lt_of_le k.isLt p.phase_capacity⟩

def inputSize (s : State L R B b d w) : ℕ := min (decodeWords s.inputCount) R
def outputSize (s : State L R B b d w) : ℕ := min (decodeWords s.outputCount) (R-1)

def converter (p : Program L R B b d w) (n : ℕ) (hn : n ≤ R) :
    PhysicalNormalizationLayout.Program R B b d w :=
  ⟨n,hn,hn.trans_lt p.counter_capacity,p.positive_region,p.positive_block,
    p.block_ratio,p.phase_capacity,p.padding⟩

def inputProgram (p : Program L R B b d w) (s : State L R B b d w) :=
  converter p (inputSize s) (Nat.min_le_right _ _)
def outputProgram (p : Program L R B b d w) (s : State L R B b d w) :=
  converter p (outputSize s) ((Nat.min_le_right _ _).trans (Nat.sub_le _ _))

def expandView (disk : Disk R B w) : PhysicalNormalizationLayout.Disk R B w
  | .inl a => disk (.inl a)
  | .inr a => disk (.inr (.inl a))
def compactView (disk : Disk R B w) : PhysicalNormalizationLayout.Disk R B w
  | .inl a => disk (.inr (.inl a))
  | .inr a => disk (.inr (.inr a))
def installExpand (old : Disk R B w) (new : PhysicalNormalizationLayout.Disk R B w) : Disk R B w
  | .inl a => new (.inl a)
  | .inr (.inl a) => new (.inr a)
  | .inr (.inr a) => old (.inr (.inr a))
def installCompact (old : Disk R B w) (new : PhysicalNormalizationLayout.Disk R B w) : Disk R B w
  | .inl a => old (.inl a)
  | .inr (.inl a) => new (.inl a)
  | .inr (.inr a) => new (.inr a)
def installCore (old : Disk R B w) (new : Normalization.Disk R B (Word w)) : Disk R B w
  | .inl a => old (.inl a)
  | .inr (.inl a) => new a
  | .inr (.inr a) => old (.inr (.inr a))

def expandState (s : State L R B b d w) : PhysicalNormalizationLayout.State R B b d w :=
  ⟨s.buffer,s.scratch,s.counter,s.phase,expandView s.disk⟩
def compactState (s : State L R B b d w) : PhysicalNormalizationLayout.State R B b d w :=
  ⟨s.buffer,s.scratch,s.counter,s.phase,compactView s.disk⟩
def coreState (s : State L R B b d w) : FixedPolicyNormalization.State L B R w :=
  ⟨⟨s.ram,s.buffer,fun a => s.disk (.inr (.inl a))⟩,s.phase⟩

def putExpand (s : State L R B b d w) (t : PhysicalNormalizationLayout.State R B b d w) :=
  {s with buffer:=t.buffer,scratch:=t.scratch,counter:=t.counter,phase:=t.phase, disk:=installExpand s.disk t.disk}
def putCompact (s : State L R B b d w) (t : PhysicalNormalizationLayout.State R B b d w) :=
  {s with buffer:=t.buffer,scratch:=t.scratch,counter:=t.counter,phase:=t.phase, disk:=installCompact s.disk t.disk}
def putCore (s : State L R B b d w) (t : FixedPolicyNormalization.State L B R w) :=
  {s with ram:=t.data.ram,buffer:=t.data.buffer,phase:=t.phase, disk:=installCore s.disk t.data.disk}
```

[CodedSorting/Shared/Memory/NormalizationController.lean](../CodedSorting/Shared/Memory/NormalizationController.lean)

```lean
def step (p : Program L R B b d w) (s : State L R B b d w) : State L R B b d w × ℕ :=
  match s.stage.val with
  | 0 =>
      if decodeWords s.counter  <  inputSize s then
        let e := PhysicalNormalizationLayout.run (inputProgram p s) 7 (expandState s)
        (putExpand s e.1,e.2)
      else ({s with stage:=code p 1,phase:=code p 0},0)
  | 1 =>
      if p.policy s.ram = none then
        ({s with stage:=code p 2,phase:=code p 0,counter:=PhysicalNormalizationLayout.counterCode d w 0, buffer:=fun _=>p.padding,scratch:=fun _=>p.padding},0)
      else
        let e := FixedPolicyNormalization.run p.block_ratio (by have := p.phase_capacity; omega) p.padding
          ⟨p.policy⟩ 2 (coreState s)
        (putCore s e.1,e.2)
  | 2 =>
      if decodeWords s.counter  <  outputSize s then
        let e := PhysicalNormalizationCompact.run (outputProgram p s) 8 (compactState s)
        (putCompact s e.1,e.2)
      else ({s with stage:=code p 3},0)
  | _ => (s,0)
```

</details>

<details>
<summary>点击展开：主排序算法（阶段 1）的物理状态与单步计费源码</summary>

[CodedSorting/Shared/Programs/Normalization.lean](../CodedSorting/Shared/Programs/Normalization.lean)

```lean
structure PhysicalState (L B D : ℕ) (Word : Type*) where
  ram : Words L Word
  buffer : Words B Word
  disk : Disk D B Word
```

[CodedSorting/Shared/Programs/FixedPolicyNormalization.lean](../CodedSorting/Shared/Programs/FixedPolicyNormalization.lean)

```lean
structure Program (L b D w : ℕ) where
  policy : ControlledNormalization.Policy L b D (Word w)

/-- All data-dependent resident state: L payload/control words from the source
machine, B transfer words, and ONE additional phase word. -/
structure State (L B D w : ℕ) where
  data : PhysicalState L B D (Word w)
  phase : Word w
```

[CodedSorting/Shared/Programs/FixedPolicyNormalization.lean](../CodedSorting/Shared/Programs/FixedPolicyNormalization.lean)

```lean
def code (hcap : 4 ≤ 2^w) (k : Fin 4) : Word w :=
  ⟨k.val, lt_of_lt_of_le k.isLt hcap⟩
```

[CodedSorting/Shared/Programs/FixedPolicyNormalization.lean](../CodedSorting/Shared/Programs/FixedPolicyNormalization.lean)

```lean
def ready (hcap : 4 ≤ 2^w) (s : PhysicalState L B D (Word w)) : State L B D w :=
  ⟨s, code hcap 0⟩
```

[CodedSorting/Shared/Programs/FixedPolicyNormalization.lean](../CodedSorting/Shared/Programs/FixedPolicyNormalization.lean)

```lean
def step (hb : b ≤ B) (hcap : 4 ≤ 2^w) (padding : Word w)
    (p : Program L b D w) (s : State L B D w) : State L B D w × ℕ :=
  match s.phase.val with
  | 0 => match p.policy s.data.ram with
    | none => (⟨s.data, code hcap 3⟩, 0)
    | some i => match i.operation with
      | .localOp f =>
          (⟨{s.data with ram := i.resume (f s.data.ram)}, code hcap 3⟩, 0)
      | .read address _ =>
          (⟨{s.data with buffer := s.data.disk address}, code hcap 1⟩, 1)
      | .write _ window =>
          (⟨{s.data with buffer := pack padding (slice s.data.ram window)},
            code hcap 2⟩, 0)
  | 1 => match p.policy s.data.ram with
    | some i => match i.operation with
      | .read _ window =>
          (ready hcap {s.data with ram := i.resume (load s.data.ram window (blockPrefix hb s.data.buffer))}, 0)
      | _ => (ready hcap s.data, 0)
    | none => (ready hcap s.data, 0)
  | 2 => match p.policy s.data.ram with
    | some i => match i.operation with
      | .write address _ =>
          (ready hcap {s.data with ram := i.resume s.data.ram, disk := Function.update s.data.disk address s.data.buffer}, 1)
      | _ => (ready hcap s.data, 0)
    | none => (ready hcap s.data, 0)
  | _ => (ready hcap s.data, 0)

def run (hb : b ≤ B) (hcap : 4 ≤ 2^w) (padding : Word w)
    (p : Program L b D w) : ℕ → State L B D w → State L B D w × ℕ
  | 0, s => (s, 0)
  | fuel+1, s =>
      let first := step hb hcap padding p s
      let rest := run hb hcap padding p fuel first.1
      (rest.1, first.2+rest.2)
```

</details>

<details>
<summary>点击展开：内存窗口与复制操作（<code>Window</code>、<code>load</code>、<code>slice</code>、<code>blockPrefix</code>、<code>pack</code>）源码</summary>

[CodedSorting/Shared/Programs/Normalization.lean](../CodedSorting/Shared/Programs/Normalization.lean)

```lean
structure Window (L b : ℕ) where
  base : ℕ
  fits : base + b ≤ L

/-- Copy a block into the designated existing RAM window. -/
def load (ram : Words L Word) (w : Window L b) (block : Words b Word) :
    Words L Word := fun j =>
  if h : w.base ≤ j.val ∧ j.val < w.base + b then
    block ⟨j.val - w.base, by omega⟩
  else ram j

/-- Read the designated RAM window without allocating another RAM array. -/
def slice (ram : Words L Word) (w : Window L b) : Words b Word := fun j =>
  ram ⟨w.base + j.val, by have := w.fits; have := j.isLt; omega⟩

/-- Valid logical data is the blockPrefix of its own physical block. -/
def blockPrefix (h : b ≤ B) (block : Words B Word) : Words b Word :=
  fun j => block (Fin.castLE h j)

/-- Fill one physical transfer buffer; the unused suffix is irrelevant. -/
def pack (padding : Word) (block : Words b Word) : Words B Word := fun j =>
  if h : j.val < b then block ⟨j.val, h⟩ else padding
```

</details>

<details>
<summary>点击展开：转换程序的计数器与缓冲区切片（<code>extract</code>、<code>patchBuffer</code>）源码</summary>

[CodedSorting/Interchange/Framework/Memory/PhysicalNormalizationLayout.lean](../CodedSorting/Interchange/Framework/Memory/PhysicalNormalizationLayout.lean)

```lean
structure Program (R B b d w : ℕ) where
  blocks : ℕ
  block_bound : blocks ≤ R
  counter_bound : blocks < (2^w)^d
  positive_region : 0<R
  positive_block : 0<B
  block_ratio : b≤B
  phase_capacity : 8≤2^w
  padding : Word w
```

[CodedSorting/Shared/Words/WordConvention.lean](../CodedSorting/Shared/Words/WordConvention.lean)

```lean
def decodeWords {count w : ℕ} (words : Words count w) : ℕ :=
  (finFunctionFinEquiv words).val
```

[CodedSorting/Interchange/Framework/Memory/PhysicalNormalizationLayout.lean](../CodedSorting/Interchange/Framework/Memory/PhysicalNormalizationLayout.lean)

```lean
def phaseCode (p : Program R B b d w) (k : Fin 8) : Word w :=
  ⟨k.val,lt_of_lt_of_le k.isLt p.phase_capacity⟩

def counterCode (d w j : ℕ) : Words d w :=
  finFunctionFinEquiv.symm ⟨j % (2^w)^d,Nat.mod_lt _ (by positivity)⟩

@[simp] theorem decode_counterCode (j : ℕ) :
    decodeWords (counterCode d w j) = j % (2^w)^d := by
  simp [counterCode,decodeWords]

/-- Addresses are evaluated from the counted counter. Live loop iterations
have j<R; the modular fallback merely makes the fixed program total. -/
def index (p : Program R B b d w) (j : ℕ) : Fin R :=
  ⟨j%R,Nat.mod_lt _ p.positive_region⟩

def current (s : State R B b d w) : ℕ := decodeWords s.counter

def nextPhase (p : Program R B b d w) (k : Fin 8) (s : State R B b d w) :=
  {s with phase := phaseCode p k}
```

[CodedSorting/Interchange/Framework/Memory/LayoutMachine.lean](../CodedSorting/Interchange/Framework/Memory/LayoutMachine.lean)

```lean
def extract (B b start block : ℕ) (hB : 0 < B)
    (buffer : Fin B → Value) (scratch : Fin b → Value) : Fin b → Value := fun i =>
  if (start+i.val) / B = block then
    buffer ⟨(start+i.val) % B, Nat.mod_lt _ hB⟩ else scratch i
```

[CodedSorting/Interchange/Framework/Memory/LayoutMachine.lean](../CodedSorting/Interchange/Framework/Memory/LayoutMachine.lean)

```lean
def patchBuffer (B b start block : ℕ) (scratch : Fin b → Value)
    (old : Fin B → Value) : Fin B → Value := fun i =>
  if h : start ≤ block*B+i.val ∧ block*B+i.val < start+b then
    scratch ⟨block*B+i.val-start, by omega⟩ else old i
```

</details>

<details>
<summary>点击展开：输入、输出块格式转换（阶段 0 与阶段 2）的物理读写与计费源码</summary>

[CodedSorting/Interchange/Framework/Memory/PhysicalNormalizationLayout.lean](../CodedSorting/Interchange/Framework/Memory/PhysicalNormalizationLayout.lean)

```lean
def step (p : Program R B b d w) (s : State R B b d w) : State R B b d w × ℕ :=
  let j := current s
  if j < p.blocks then
    match s.phase.val with
    | 0 => (nextPhase p 1 {s with scratch := fun _ => p.padding},0)
    | 1 => (nextPhase p 2 {s with buffer := s.disk (.inl (index p (j*b/B)))},1)
    | 2 => (nextPhase p 3 {s with scratch := LayoutConversion.extract B b (j*b) (j*b/B) p.positive_block s.buffer s.scratch},0)
    | 3 => (nextPhase p 4 {s with buffer := s.disk (.inl (index p (j*b/B+1)))},1)
    | 4 => (nextPhase p 5 {s with scratch := LayoutConversion.extract B b (j*b) (j*b/B+1) p.positive_block s.buffer s.scratch},0)
    | 5 => (nextPhase p 6 {s with buffer := Normalization.pack p.padding s.scratch},0)
    | 6 => (nextPhase p 0 {s with counter := counterCode d w (j+1), disk := Function.update s.disk (.inr (index p j)) s.buffer},1)
    | _ => (s,0)
  else (s,0)

def run (p : Program R B b d w) : ℕ → State R B b d w → State R B b d w × ℕ
  | 0,s => (s,0)
  | fuel+1,s =>
      let first := step p s
      let rest := run p fuel first.1
      (rest.1,first.2+rest.2)
```

[CodedSorting/Shared/Memory/PhysicalNormalizationCompact.lean](../CodedSorting/Shared/Memory/PhysicalNormalizationCompact.lean)

```lean
def step (p : Program R B b d w) (s : State R B b d w) : State R B b d w × ℕ :=
  let j := current s
  if j<p.blocks then
    match s.phase.val with
    | 0 => (nextPhase p 1 {s with buffer := s.disk (.inl (index p j))},1)
    | 1 => (nextPhase p 2 {s with scratch := fun i => s.buffer (i.castLE p.block_ratio)},0)
    | 2 => (nextPhase p 3 {s with buffer := s.disk (.inr (index p (j*b/B)))},1)
    | 3 => (nextPhase p 4 {s with buffer := LayoutConversion.patchBuffer B b (j*b) (j*b/B) s.scratch s.buffer},0)
    | 4 => (nextPhase p 5 {s with disk := Function.update s.disk (.inr (index p (j*b/B))) s.buffer},1)
    | 5 => (nextPhase p 6 {s with buffer := s.disk (.inr (index p (j*b/B+1)))},1)
    | 6 => (nextPhase p 7 {s with buffer := LayoutConversion.patchBuffer B b (j*b) (j*b/B+1) s.scratch s.buffer},0)
    | 7 => (nextPhase p 0 {s with counter := counterCode d w (j+1), disk := Function.update s.disk (.inr (index p (j*b/B+1))) s.buffer},1)
    | _ => (s,0)
  else (s,0)

def run (p : Program R B b d w) : ℕ → State R B b d w → State R B b d w × ℕ
  | 0,s => (s,0)
  | fuel+1,s =>
      let first := step p s
      let rest := run p fuel first.1
      (rest.1,first.2+rest.2)
```

</details>

### 2.3 核验三：内存不超过 $M$ 字与多项式磁盘空间

**1. 常驻内存字数的完整核算 (`Fintype.card (ResidentIndex q) ≤ M`)**。

在 `NormalGuarantee` 中，内存上界写为 `Fintype.card (ResidentIndex q) ≤ M`，其中 `Fintype.card T` 表示有限类型 `T` 的元素基数。由于不交并类型 `Fin A ⊕ Fin B` 的基数恰好为 $A + B$，[NormalizationFrames.lean](../CodedSorting/Sorting/Resources/Framework/NormalizationFrames.lean) 通过 `ResidentIndex q` 将机器状态 `MachineState q` 中除磁盘 `disk` 以外的**所有内存数组与控制寄存器**（连同额外预留的一个完整磁盘地址端口 `port`）拼接为一个统一的索引集合，并通过映射函数 `resident` 与实际状态字段建立一一对应：

| 状态中的内存字段 | 对应索引项 | 用途说明 | 占用机器字数 |
| --- | --- | --- | --- |
| `s.ram` | `Fin q.ramWords` | 算法工作内存（含流缓冲、排序记录及当前层递归控制变量） | $L = \mathtt{q.ramWords}$ |
| `s.buffer` | `Fin q.B` | 物理磁盘块中转缓冲区（附录 A.3） | $B$ |
| `s.scratch` | `Fin q.block` | 块格式转换时暂存的一个逻辑块 | $\beta = \mathtt{q.block}$ |
| `s.counter`, `s.inputCount`, `s.outputCount` | 三个 `Fin q.digits` | 当前块计数器与输入、输出块数寄存器 | $3d$（其中 $d = \mathtt{q.digits}$） |
| `s.phase`, `s.stage` | `Fin 2` | 内部相位寄存器与外层阶段寄存器 | $2$ |
| `port` | `Fin (q.digits+1)` | 另行预留的完整磁盘地址寄存器 | $d + 1$ |
| **合计 (`Fintype.card (ResidentIndex q)`)** | | **机器常驻内存总字数** | **$L + B + \beta + 4d + 3 \le M$** |

<details>
<summary>点击展开：<code>ResidentIndex</code> 与机器状态字段的一一对应源码</summary>

[CodedSorting/Sorting/Resources/Framework/NormalizationFrames.lean](../CodedSorting/Sorting/Resources/Framework/NormalizationFrames.lean)

```lean
abbrev MachineState (q : Configuration) :=
  CommonNormalizationController.State q.ramWords (q.N^q.exponent) q.B q.block q.digits q.w

/-- These are the actual fields of MachineState, plus its separately
reserved address port. The source RAM is the injective pack above. -/
abbrev ResidentIndex (q : Configuration) :=
  (Fin q.ramWords ⊕ Fin q.B) ⊕
    ((Fin q.block ⊕ Fin q.digits) ⊕
      ((Fin q.digits ⊕ Fin q.digits) ⊕ (Fin 2 ⊕ Fin (q.digits+1))))

def resident (q : Configuration) (s : MachineState q) (port : Words (q.digits+1) q.w) :
    ResidentIndex q → Word q.w
  | .inl (.inl i) => s.ram i
  | .inl (.inr i) => s.buffer i
  | .inr (.inl (.inl i)) => s.scratch i
  | .inr (.inl (.inr i)) => s.counter i
  | .inr (.inr (.inl (.inl i))) => s.inputCount i
  | .inr (.inr (.inl (.inr i))) => s.outputCount i
  | .inr (.inr (.inr (.inl i))) => if i.val=0 then s.phase else s.stage
  | .inr (.inr (.inr (.inr i))) => port i
```

</details>

*(注：依照论文附录 A.2 与附录 D，当递归进入子调用时，暂停的父调用控制状态与缓冲区均被写入磁盘工作区，当前调用复用同一片长度为 $L$ 的工作内存 `ram`；而存在量词中的步数参数 `fuel` 仅用于刻画有限次迭代的数学上界，机器运行时的实际控制位置完全由上述 `counter`、`phase`、`stage` 及 `ram` 中的控制字维护。)*

**2. 多项式磁盘空间上界**。

由于 `Address (q.N^q.exponent)` 由三个大小为 $R = N^E$ 的区域组成，磁盘总块数 `Fintype.card (Address ...)` 满足 $3 N^E \le N^{E+2}$，乘以块大小 $B$ 后的磁盘总字数满足 $3 N^E B \le N^{E+3}$。其中指数 $E = \mathtt{exponent}(\kappa)$ 仅由固定字长常数 $\kappa$ 决定，从而验证了磁盘空间为 $N$ 的多项式规模。

---

## 3. 小内存分支 `SmallGuarantee`

当 $M < \mathrm{Mcut}(c,\kappa)$ 时，物理内存小于固定常数阈值，算法调用论文第 8.3 节（引理 8.3）的小内存排序（当 $w \ge \lceil\log_2 N\rceil$ 时采用直接基数排序，当 $w < \lceil\log_2 N\rceil$ 时采用计数排序）。[Proof.lean](../CodedSorting/Sorting/Theorem31/Proof.lean) 中的 `SmallGuarantee` 给出了与常规分支相应的排序与资源保证：

<details>
<summary>点击展开：小内存分支 <code>SmallGuarantee</code> 的完整声明源码</summary>

```lean
def SmallGuarantee (c : ℕ) (κ : ℝ) (N M B w : ℕ) (hB : 0<B) : Prop :=
  ∃ (code : List (TwoWordSmallMemorySorting.Stage B w)) (allocation : ℕ)
    (output : List (Word w) → List (Word w)),
    TwoWordSmallMemoryFootprint.BoundedCode allocation code ∧
    allocation*B≤smallSpaceBound c κ N ∧
    ∀ (s : TwoWordBlockLift.State B (Word w)) (xs : List (Word w)),
      xs.length=N → TwoWordBlockFormat.File hB s.disk xs →
      ∃t cost, TwoWordSmallMemorySorting.Executes hB code s t cost ∧
        TwoWordBlockFormat.File hB t.disk (output xs) ∧
        (output xs).Perm xs ∧ (output xs).Pairwise (fun x y=>x.val≤y.val) ∧
        Fintype.card (Fin B ⊕ Fin B)≤M ∧
        (cost : ℝ)≤coefficient c κ*((N : ℝ)/B)*factor N M B
```

</details>

**`SmallGuarantee` 的分块逻辑解析：**

1. **先于输入选定程序与磁盘配额（外层存在量词 `∃ code allocation output`）**：
   存在指令段列表 `code`、磁盘块分配上限 `allocation` 以及输出映射 `output`，满足地址边界检查 `BoundedCode allocation code`，且分配的磁盘总字数 `allocation * B` 不超过多项式上界 `smallSpaceBound c κ N`。由于 `∃ code` 位于全称量词 `∀ s xs` 之前，同一指令序列 `code` 对所有长度为 $N$ 的输入列表通用。

2. **对任意初始状态与输入执行并验证结果（内层 `∀ s xs` 与 `∃ t cost`）**：
   对于任意初始状态 `s` 和长度为 $N$、按紧凑格式存放在磁盘 `s.disk` 上的输入列表 `xs`（`File hB s.disk xs`），存在终止状态 `t` 和累计 I/O 次数 `cost`，使得：

   * 从初态 `s` 运行程序 `code` 在有限步内完成并到达终态 `t`，累计费用为 `cost`（`Executes hB code s t cost`）；
   * 终态磁盘 `t.disk` 按相同紧凑格式存放输出列表 `output xs`，且 `output xs` 是 `xs` 的非递减排列（`Perm` 与 `Pairwise`）；
   * 内存仅占用两个大小为 $B$ 字的物理块缓冲区（`Fintype.card (Fin B ⊕ Fin B) ≤ M`，即 $2B \le M$），且累计 I/O 次数 `cost` 满足与常规内存分支完全相同的复杂度上界。

### 3.1 核验一：两个物理块缓冲区与紧凑磁盘文件

在 [SmallSort.lean](../CodedSorting/Sorting/SmallMemory/SmallSort.lean) 中，小内存机器的状态 `State B W` 仅包含左、右两个物理块缓冲区 `left, right : Buffer B W`（其中 `Buffer B W` 即 `Fin B → W`）以及磁盘 `disk : ℕ → Buffer B W`。文件谓词 `File hB disk xs` 要求磁盘第 `i / B` 块的第 `i % B` 个字等于 `xs.get i`，与常规分支的紧凑块格式完全一致。

机器仅支持五种基本命令 `Command B W`：

* `.readLeft a` 与 `.writeLeft a`：在固定物理块地址 `a` 与左缓冲区 `left` 之间整块读取或写入；
* `.readRight a` 与 `.writeRight a`：根据当前双缓冲区内容 `(s.left, s.right)` 计算目标物理块地址 `a (s.left, s.right)`，与右缓冲区 `right` 进行整块读取或写入；
* `.cpu f`：仅根据当前双缓冲区内容 `(s.left, s.right)` 计算并更新双缓冲区，不访问磁盘。

<details>
<summary>点击展开：紧凑文件 <code>File</code>、双缓冲状态 <code>State</code> 与五种基本命令源码</summary>

[CodedSorting/Sorting/SmallMemory/SmallSort.lean](../CodedSorting/Sorting/SmallMemory/SmallSort.lean)

```lean
def cell (hB : 0<B) (i : ℕ) : Fin B := ⟨i%B,Nat.mod_lt _ hB⟩
def wordAt (hB : 0<B) (disk : ℕ→Buffer B W) (i : ℕ) : W := disk (i/B) (cell hB i)
def File (hB : 0<B) (disk : ℕ→Buffer B W) (xs : List W) : Prop :=
  ∀ j : Fin xs.length,wordAt hB disk j.val=xs.get j
```

[CodedSorting/Sorting/SmallMemory/SmallSort.lean](../CodedSorting/Sorting/SmallMemory/SmallSort.lean)

```lean
abbrev Buffer (B : ℕ) (W : Type*) := Fin B → W
structure State (B : ℕ) (W : Type*) where
  left : Buffer B W
  right : Buffer B W
  disk : ℕ → Buffer B W

inductive Command (B : ℕ) (W : Type*) where
  | readLeft (address : ℕ)
  | readRight (address : Buffer B W × Buffer B W → ℕ)
  | writeLeft (address : ℕ)
  | writeRight (address : Buffer B W × Buffer B W → ℕ)
  | cpu (f : Buffer B W × Buffer B W → Buffer B W × Buffer B W)

def step (cmd : Command B W) (s : State B W) : State B W :=
  match cmd with
  | .readLeft a => {s with left := s.disk a}
  | .readRight a => {s with right := s.disk (a (s.left,s.right))}
  | .writeLeft a => {s with disk := Function.update s.disk a s.left}
  | .writeRight a => {s with disk := Function.update s.disk (a (s.left,s.right)) s.right}
  | .cpu f => {s with left := (f (s.left,s.right)).1, right := (f (s.left,s.right)).2}
```

</details>

### 3.2 核验二：小内存分支的执行与 I/O 计费

[SmallSort.lean](../CodedSorting/Sorting/SmallMemory/SmallSort.lean) 对上述五种基本命令的单步计费函数 `cost` 定义如下：

```lean
def cost : Command B W → ℕ
  | .cpu _ => 0
  | _ => 1
```

纯内存计算命令 `.cpu _` 计 `0` 次 I/O，其余四条整块读写命令均计 `1` 次 I/O。

外层程序由顺序指令段 `.straight`、块格式转换循环段 `.loop` 以及排序主体 `.core` 组成（在 `.core` 中，每个待访问字单独存放在一个物理块的首字位置 `⟨0, hB⟩`，由编译函数 `compile` 逐条翻译为上述五种物理块命令）。

在下方源码中，完整执行关系 `Executes` 由归纳类型（`inductive Executes ... where`）定义：

* **顺序段（`straight` 规则）**：通过列表递归函数 `execute` 依次执行列表中（`[]` 为空列表，`cmd :: rest` 为首尾拼接）的每条命令，并通过 `transfers` 将每条命令的 `cost` 累加；
* **循环段（`loop` 与 `LoopExecutes` 规则）**：每次迭代先执行 `check`，即调用 `.readLeft` 读取磁盘上的循环标志块（计 **`1` 次 I/O**）。若首字等于停机标志 `halt`（`stop` 规则），循环终止并计入这 `1` 次检查 I/O；若不等于 `halt`（`more` 规则），则执行一轮循环体 `body` 并继续下一轮检查，总费用累加为 `1 + transfers body + 后续费用`。

因为归纳关系中的每条推导树均由有限步构造而成，`Executes hB code s t cost` 严格保证了程序在有限步内停机于状态 `t`，且 `cost` 等于全过程所有物理块读写的总和。

<details>
<summary>点击展开：顺序执行与外层程序段 <code>Executes</code> 源码</summary>

[CodedSorting/Sorting/SmallMemory/SmallSort.lean](../CodedSorting/Sorting/SmallMemory/SmallSort.lean)

```lean
def execute : List (Command B W) → State B W → State B W
  | [],s => s
  | cmd::rest,s => execute rest (step cmd s)
def transfers : List (Command B W) → ℕ
  | [] => 0
  | cmd::rest => cost cmd+transfers rest
```

[CodedSorting/Sorting/SmallMemory/SmallMemorySorting.lean](../CodedSorting/Sorting/SmallMemory/SmallMemorySorting.lean)

```lean
inductive Stage (B w : ℕ) where
  | straight (body : List (Command B (Word w)))
  | loop (p : TwoWordUniformBlockFormat.LoopProgram B (Word w))
  | core (base : ℕ) (body : List (TwoWordRadixPreparedBuild.Stage (Word w)))

inductive Executes {B w : ℕ} (hB : 0<B) :
    List (Stage B w) → State B (Word w) → State B (Word w) → ℕ → Prop where
  | done (s : State B (Word w)) : Executes hB [] s s 0
  | straight (body : List (Command B (Word w))) (rest : List (Stage B w))
      (s t : State B (Word w)) (cost : ℕ)
      (tail : Executes hB rest (TwoWordBlockLift.execute body s) t cost) :
      Executes hB (.straight body::rest) s t (TwoWordBlockLift.transfers body+cost)
  | loop (p : TwoWordUniformBlockFormat.LoopProgram B (Word w)) (rest : List (Stage B w))
      (s mid t : State B (Word w)) (ca cb : ℕ)
      (first : TwoWordUniformBlockFormat.Executes hB p s mid ca)
      (tail : Executes hB rest mid t cb) :
      Executes hB (.loop p::rest) s t (ca+cb)
  | core (base : ℕ) (body : List (TwoWordRadixPreparedBuild.Stage (Word w)))
      (rest : List (Stage B w)) (s mid t : State B (Word w)) (ca cb : ℕ)
      (first : TwoWordBlockLift.Executes hB base body s mid ca)
      (tail : Executes hB rest mid t cb) :
      Executes hB (.core base body::rest) s t (ca+cb)
```

</details>

<details>
<summary>点击展开：块压缩循环的停止检查与计费源码</summary>

[CodedSorting/Sorting/SmallMemory/Uniform/BlockCompress.lean](../CodedSorting/Sorting/SmallMemory/Uniform/BlockCompress.lean)

```lean
structure LoopProgram (B : ℕ) (W : Type*) where
  flagAddress : ℕ
  halt : W
  body : List (Command B W)

def check {W : Type*} (p : LoopProgram B W) (s : State B W) : State B W :=
  step (.readLeft p.flagAddress) s
def next {W : Type*} (p : LoopProgram B W) (s : State B W) : State B W :=
  execute p.body (check p s)
inductive Executes {W : Type*} (hB : 0<B) (p : LoopProgram B W) :
    State B W → State B W → ℕ → Prop where
  | stop (s : State B W) (h : (check p s).left ⟨0,hB⟩=p.halt) :
      Executes hB p s (check p s) 1
  | more (s t : State B W) (cost : ℕ)
      (h : (check p s).left ⟨0,hB⟩≠p.halt)
      (rest : Executes hB p (next p s) t cost) :
      Executes hB p s t (1+transfers p.body+cost)
```

</details>

<details>
<summary>点击展开：排序主体 <code>core</code> 的指令编译与循环执行源码</summary>

[CodedSorting/Sorting/SmallMemory/PhysicalAddresses.lean](../CodedSorting/Sorting/SmallMemory/PhysicalAddresses.lean)

```lean
inductive Command (W : Type*) where
  | readLeft (a : ℕ)
  | readRight (a : ℕ)
  | readRightAt (a : Resident W → ℕ)
  | writeLeft (a : ℕ)
  | writeRight (a : Resident W → ℕ)
  | localOp (f : Resident W → Resident W)
```

[CodedSorting/Sorting/SmallMemory/Uniform/Loop.lean](../CodedSorting/Sorting/SmallMemory/Uniform/Loop.lean)

```lean
structure Program (W : Type*) where
  pcAddress : ℕ
  halt : W
  body : List (Command W)
```

[CodedSorting/Sorting/SmallMemory/Radix/Initialize.lean](../CodedSorting/Sorting/SmallMemory/Radix/Initialize.lean)

```lean
inductive Stage (W : Type*) where
  | straight (code : List (TwoWordPhysicalAddresses.Command W))
  | loop (program : Physical.Program W)
```

[CodedSorting/Sorting/SmallMemory/SmallSort.lean](../CodedSorting/Sorting/SmallMemory/SmallSort.lean)

```lean
def compile (hB : 0<B) (base : ℕ) : TwoWordPhysicalAddresses.Command W → Command B W
  | .readLeft a => .readLeft (base+a)
  | .readRight a => .readRight (fun _ => base+a)
  | .readRightAt a => .readRight (fun r => base+a (r.1 ⟨0,hB⟩,r.2 ⟨0,hB⟩))
  | .writeLeft a => .writeLeft (base+a)
  | .writeRight a => .writeRight (fun r => base+a (r.1 ⟨0,hB⟩,r.2 ⟨0,hB⟩))
  | .localOp f => .cpu (fun r =>
      let v := f (r.1 ⟨0,hB⟩,r.2 ⟨0,hB⟩)
      (fun _ => v.1,fun _ => v.2))
```

[CodedSorting/Sorting/SmallMemory/SmallSort.lean](../CodedSorting/Sorting/SmallMemory/SmallSort.lean)

```lean
def check (base : ℕ) (p : Physical.Program W) (s : State B W) :=
  step (.readLeft (base+p.pcAddress)) s
def next (hB : 0<B) (base : ℕ) (p : Physical.Program W) (s : State B W) :=
  execute (p.body.map (compile hB base)) (check base p s)
```

[CodedSorting/Sorting/SmallMemory/SmallSort.lean](../CodedSorting/Sorting/SmallMemory/SmallSort.lean)

```lean
inductive LoopExecutes (hB : 0<B) (base : ℕ) (p : Physical.Program W) :
    State B W → State B W → ℕ → Prop where
  | stop (s : State B W) (h : (check base p s).left ⟨0,hB⟩=p.halt) :
      LoopExecutes hB base p s (check base p s) 1
  | more (s t : State B W) (c : ℕ)
      (h : (check base p s).left ⟨0,hB⟩≠p.halt)
      (rest : LoopExecutes hB base p (next hB base p s) t c) :
      LoopExecutes hB base p s t (1+transfers (p.body.map (compile hB base))+c)
```

[CodedSorting/Sorting/SmallMemory/SmallSort.lean](../CodedSorting/Sorting/SmallMemory/SmallSort.lean)

```lean
inductive Executes (hB : 0<B) (base : ℕ) :
    List (TwoWordRadixPreparedBuild.Stage W) → State B W → State B W → ℕ → Prop where
  | done (s : State B W) : Executes hB base [] s s 0
  | straight (code : List (TwoWordPhysicalAddresses.Command W))
      (rest : List (TwoWordRadixPreparedBuild.Stage W)) (s t : State B W) (c : ℕ)
      (tail : Executes hB base rest (execute (code.map (compile hB base)) s) t c) :
      Executes hB base (.straight code::rest) s t (transfers (code.map (compile hB base))+c)
  | loop (p : Physical.Program W) (rest : List (TwoWordRadixPreparedBuild.Stage W))
      (s mid t : State B W) (ca cb : ℕ) (first : LoopExecutes hB base p s mid ca)
      (tail : Executes hB base rest mid t cb) :
      Executes hB base (.loop p::rest) s t (ca+cb)
```

</details>

### 3.3 核验三：小内存分支的磁盘空间上界与控制约定

**1. 磁盘地址边界 (`BoundedCode allocation code`)**。

虽然小内存状态的磁盘类型写作 `ℕ → Buffer B W`，但谓词 `BoundedCode allocation code` 对程序中的所有阶段与指令进行了静态边界约束（`∀ st ∈ code`）：不仅要求所有固定读写地址和循环标志地址严格小于 `allocation`，而且对依赖缓冲区内容的动态寻址命令（`.readRight a` 与 `.writeRight a`），通过全称量词 `∀ r, a r < L` 要求**在任意可能的缓冲区内容 `r` 下，计算出的目标块地址均严格小于 `allocation`**。
结合 `allocation * B ≤ smallSpaceBound c κ N`，所有被访问的磁盘字数被严格限制在 $N$ 的固定多项式 $(N + 13 + 6 N^{2u})N + (2c + 16)N^2$（其中 $u = \max\{1, \lceil\kappa\rceil\}$）之内。

**2. 程序控制约定**。

与论文第 8.3 节及附录 D 一致，数据内存仅包含 `left` 和 `right` 两个块缓冲区（合计 $2B \le M$ 字）。当 $w \ge \lceil\log_2 N\rceil$ 时，循环游标和停止标志存放在磁盘块中，其每次读写均已计入上述 `cost`；当 $w < \lceil\log_2 N\rceil$ 时，预定操作序列的当前执行步编号由控制器在 $M$ 个数据字之外维护。

<details>
<summary>点击展开：<code>BoundedCode</code> 磁盘地址界与多项式上界 <code>smallSpaceBound</code> 源码</summary>

[CodedSorting/Sorting/SmallMemory/PublicUnrolledBlockSort.lean](../CodedSorting/Sorting/SmallMemory/PublicUnrolledBlockSort.lean)

```lean
def BoundedStage (L : ℕ) : Stage B w → Prop
  | .straight body => TwoWordBlockFootprint.BoundedCode L body
  | .loop p => TwoWordUniformBlockFormat.BoundedProgram L p
  | .core base body => ∃ R, base+R≤L ∧ TwoWordRadixFootprint.BoundedCode R body

def BoundedCode (L : ℕ) (code : List (Stage B w)) : Prop := ∀st∈code,BoundedStage L st
```

[CodedSorting/Sorting/SmallMemory/Uniform/BlockCompress.lean](../CodedSorting/Sorting/SmallMemory/Uniform/BlockCompress.lean)

```lean
def BoundedProgram {W : Type*} (L : ℕ) (p : LoopProgram B W) : Prop :=
  p.flagAddress<L ∧ TwoWordBlockFootprint.BoundedCode L p.body
```

[CodedSorting/Sorting/SmallMemory/Radix/Sort.lean](../CodedSorting/Sorting/SmallMemory/Radix/Sort.lean)

```lean
def BoundedCommand (L : ℕ) : Command W → Prop
  | .readLeft a => a<L
  | .readRight a => a<L
  | .readRightAt a => ∀r,a r<L
  | .writeLeft a => a<L
  | .writeRight a => ∀r,a r<L
  | .localOp _ => True

def BoundedStage (L : ℕ) : Stage W → Prop
  | .straight cmds => ∀c∈cmds,BoundedCommand L c
  | .loop p => p.pcAddress<L ∧ ∀c∈p.body,BoundedCommand L c

def BoundedCode (L : ℕ) (code : List (Stage W)) := ∀s∈code,BoundedStage L s
```

[CodedSorting/Sorting/SmallMemory/SmallSort.lean](../CodedSorting/Sorting/SmallMemory/SmallSort.lean)

```lean
def BoundedCommand (L : ℕ) : Command B W → Prop
  | .readLeft a => a<L
  | .readRight a => ∀ r,a r<L
  | .writeLeft a => a<L
  | .writeRight a => ∀ r,a r<L
  | .cpu _ => True
def BoundedCode (L : ℕ) (code : List (Command B W)) :=
  ∀ cmd∈code,BoundedCommand L cmd
```

[CodedSorting/Sorting/Theorem31/Proof.lean](../CodedSorting/Sorting/Theorem31/Proof.lean)

```lean
def smallSpaceBound (c : ℕ) (κ : ℝ) (N : ℕ) : ℕ :=
  (N+13+6*N^(2*SmallMemorySortingRate.wordFactor κ))*N+(2*c+16)*N^2
```

</details>

---

## 4. 统一的 I/O 复杂度上界与常数依赖

无论执行常规内存分支 `NormalGuarantee` 还是小内存分支 `SmallGuarantee`，最终累计的物理块传输次数 $Q$（即 `result.2` 或 `cost`）均满足同一形式的上界：

$$Q \le \mathtt{coefficient}(c,\kappa) \cdot \frac{N}{B} \cdot \mathtt{factor}(N,M,B).$$

### 4.1 核验对数改进因子 `factor`

[Proof.lean](../CodedSorting/Sorting/Theorem31/Proof.lean) 与 [LargeMemory.lean](../CodedSorting/Sorting/Theorem31/LargeMemory.lean) 给出了 `factor` 的显式定义（此处 `(M : ℝ) / B` 与 `(N : ℝ) / B` 均为精确的实数除法）：

```lean
theorem factor_eq (N M B : ℕ) : factor N M B=GeneralWordNormalSorting.factor N M B := by
  simp only [factor,SmallMemorySortingRate.paperFactor,GeneralWordNormalSorting.factor,
    CommonLocalBudgetRate.tau,sub_sub_cancel]
```

```lean
def factor (N M B : ℕ) : ℝ :=
  1+Real.log (N : ℝ)/
    (Real.log ((M : ℝ)/B)^(1-(CodedSorting.Construction.epsilon : ℝ))*
      Real.log (M : ℝ)^(CodedSorting.Construction.epsilon : ℝ))
```

其中指数常数 $\varepsilon$ 在 [Exponent.lean](../CodedSorting/Circuit/Parameters/Exponent.lean) 中定义为精确有理数（`ℚ`）：

```lean
def epsilon : ℚ := 3 / 200000
```

即 $\varepsilon = 1.5\times 10^{-5}$。由于分母中 $\ln(M/B)$ 与 $\ln M$ 的指数之和为 $(1-\varepsilon)+\varepsilon=1$，将自然对数 `Real.log` 换底为论文所用的以 $2$ 为底的对数 $\log_2$ 时，分子与分母乘上的换底常数 $\ln 2$ 恰好约去。因此，`factor N M B` 与论文定理 3.1 公式中的括号项完全一致：

$$1+\frac{\log N}{(\log(M/B))^{1-\varepsilon}(\log M)^\varepsilon}.$$

### 4.2 地址交换的递推来源

上述指数 $1-\varepsilon$ 源自论文第 6 节的地址字段交换递归。在 [ExchangeInterface.lean](../CodedSorting/Interchange/Bounds/ExchangeInterface.lean) 中，深度为 $k$、数据量为 $V$ 比特、块比特数为 $b$、内存停止阈值为 `cutoff` 的地址交换代价上界 `costBound` 满足整数递推：

* 当 $k=0$ 或 $V \le \texttt{cutoff}$ 时，$Q(k,V) = 20(\lfloor V/b \rfloor + 1)$；
* 当 $V > \texttt{cutoff}$ 时，$Q(k+1,V) = a(\lfloor V/b \rfloor + 1) + S\,Q(k, \lfloor V/W \rfloor)$，其中 $m=512, W=24432543, S=12508242237$ 为第 5 节固定电路的参数，$a$ 是单层实现的固定费用系数。

[Resources.lean](../CodedSorting/Interchange/Recursion/Resources.lean) 中的定理 `exists_rate` 证明了存在一个与规模无关的绝对常数 $K$（代码中记为 `rateConstant`），使所有满足 $b>0$、$\texttt{cutoff}\ge Wb$ 的参数均满足 $Q(k,V) \le K\big(1 + \frac{V}{b} m^{k(1-\varepsilon)}\big)$。

<details>
<summary>点击展开：递推上界定理 <code>exists_rate</code> 源码（量词顺序 <code>∃ K, ∀ b cutoff k V</code>）</summary>

[CodedSorting/Interchange/Recursion/Resources.lean](../CodedSorting/Interchange/Recursion/Resources.lean)

```lean
theorem exists_rate :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ b cutoff k V : Nat,
      0 < b → streamCount * b ≤ cutoff →
      (costBound coefficient b cutoff k V : ℝ) ≤
        K * (1 + (V : ℝ) / b *
          (ambientDimension : ℝ) ^ ((k : ℝ) * (1 - (Construction.epsilon : ℝ)))) :=
  exists_costBound_rate coefficient
```

</details>

### 4.3 核验常数 `coefficient` 的独立性

为了确保定理中的大 $O(\cdot)$ 系数不隐含任何依赖规模参数 $N,M,B,w$ 的项，需要检查 `coefficient` 的完整参数列表、定义及其引用常数的依赖关系：

```lean
def coefficient (c : ℕ) (κ : ℝ) : ℝ := max 1
  (max (GeneralWordNormalSorting.coefficient c κ)
    (max (5000*(SmallMemorySortingRate.wordFactor κ : ℝ)*GeneralWordNormalSorting.Mcut c κ)
      (305*((c : ℝ)+2)*GeneralWordNormalSorting.Mcut c κ)))
```

`coefficient` 的参数列表**仅有字长约定常数 `(c : ℕ)` 和 `(κ : ℝ)`**，其值定义为 $1$、常规内存分支系数以及小内存两个分支系数的最大值。展开下方源码块可进一步核实：内存阈值 `Mcut c κ`、磁盘多项式指数 `exponent κ` 以及常规分支系数 `GeneralWordNormalSorting.coefficient c κ` 同样仅由固定电路常数与 $c, \kappa$ 算术组合而成，完全独立于 $N,M,B,w$ 及具体输入数据。

<details>
<summary>点击展开：内存阈值 <code>Mcut</code>、磁盘指数 <code>exponent</code> 与常规分支系数源码</summary>

[CodedSorting/Sorting/Theorem31/LargeMemory.lean](../CodedSorting/Sorting/Theorem31/LargeMemory.lean)

```lean
def inventory : SortingResourceBudget.Inventory where
  readers := 1
  writers := 0
  keys := 0
  pc := 0
  ratio := PhysicalLeafParameters.minimumRatio Construction.ExchangeSpecialization.radix 1
    Construction.streamCount
def exponent (κ : ℝ) : ℕ := CodedSorting.Construction.Sorting.CommonIntegerAllInputCapacity.exponent (wordFactor κ)
def digits (c : ℕ) (κ : ℝ) : ℕ := SortingResourceBudget.digits c (exponent κ)
def reserveSize (c : ℕ) (κ : ℝ) : ℕ :=
  SortingResourceBudget.reserve inventory c (digits c κ)
def Mcut (c : ℕ) (κ : ℝ) : ℕ := reserveSize c κ ^ 2
```

[CodedSorting/Sorting/Theorem31/LargeMemory.lean](../CodedSorting/Sorting/Theorem31/LargeMemory.lean)

```lean
def coefficient (c : ℕ) (κ : ℝ) : ℝ :=
  (2*(reserveSize c κ : ℝ)^2)*
    (1+Real.log (2*(reserveSize c κ : ℝ))/Real.log 2)^2*
    (12*22194000000*
      GlobalSortingBound.rateConstant CodedSorting.Construction.Sorting.CommonLocalBudgetRate.K CodedSorting.Construction.Sorting.CommonLocalBudgetRate.tau*
      (κ*(1+Real.log (4*(digits c κ : ℝ))/Real.log 2)+2)+2*(16 : ℝ))
```

</details>

| 参数类别 | 具体参数 | 依赖范围 | 源码位置 |
| --- | --- | --- | --- |
| **电路绝对常数** | $m=512, W=24432543, S=12508242237$ | 完全固定 | [Counts.lean](../CodedSorting/Circuit/Parameters/Counts.lean) |
| **指数绝对常数** | $\varepsilon=3/200000, \eta=33/338432$ | 完全固定 | [Exponent.lean](../CodedSorting/Circuit/Parameters/Exponent.lean) |
| **实现绝对常数** | 素数进制 `radix`、单层开销 $a$、`rateConstant` | 完全固定 | [Exchange.lean](../CodedSorting/Interchange/OneLevel/Exchange.lean)、[Resources.lean](../CodedSorting/Interchange/Recursion/Resources.lean) |
| **字长约定常数** | $c, \kappa$ | 由 $w=\Theta(\log N)$ 预先给定 | [Model.zh-CN.md](Model.zh-CN.md) |
| **顶层阈值与系数** | `Mcut c κ`、`coefficient c κ`、`exponent κ` | 仅依赖于 $c, \kappa$，对所有 $N,M,B,w$ 通用 | [LargeMemory.lean](../CodedSorting/Sorting/Theorem31/LargeMemory.lean)、[Proof.lean](../CodedSorting/Sorting/Theorem31/Proof.lean) |
| **规模与实例变量** | $N, M, B, w$ 及子问题维度 $e, V, P, G, l, k$ | 随输入规模、机器配置或递归层数变化 | 各定理与定义中的显式参数 |

---

## 5. 自动核验脚本与编译命令

在仓库根目录运行以下命令，可自动验证本页中的所有 Lean 代码摘录与仓库源码逐字一致：

```sh
python3 lean/scripts/check_release.py
```

安装仓库指定的 Lean 工具链后，运行以下命令编译全部证明并执行自动审计（[Audit.lean](../Audit.lean) 核对 `theorem_3_1` 与实现定理的类型签名并列出公理依赖；验证脚本确认依赖均在 `propext`、`Classical.choice`、`Quot.sound` 三项标准公理之内）：

```sh
cd lean
lake exe cache get
python3 scripts/verify.py
```
