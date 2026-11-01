# 复杂度系数为什么是固定常数

主定理的 I/O 上界是“一个固定系数 × 一个含规模参数的公式”。核对时要把两者分开：先固定字长约定中的 $c,\kappa$，然后允许 $N,M,B,w$ 和输入内容任意变化。

## 顶层系数

[Proof.lean](Proof.lean) 的 `coefficient c κ` 是下面四个量的最大值：

$$1,\quad C_{\mathrm{normal}}(c,\kappa),\quad5000uM_0,\quad305(c+2)M_0,$$

其中 $u=\max\{1,\lceil\kappa\rceil\}$、$M_0=\operatorname{Mcut}(c,\kappa)$。第一个量保证系数为正，其余三个分别用于以下情形：内存达到固定阈值；内存小于阈值且一个字足以表示输入位置；内存小于阈值且一个字不足以表示输入位置。后两种情形分别对应 $w\ge\lceil\log_2N\rceil$ 和 $w<\lceil\log_2N\rceil$。

这一定义只接受 `c,κ`。顶层结论对任意合法的 `N,M,B,w` 使用同一个函数值。代码中自然数到实数的转换只改变运算所在的数系。

## 内存达到固定阈值时的系数

[LargeMemory.lean](LargeMemory.lean) 将其明确写为

$$C_{\mathrm{normal}}=2C^2\left(1+\frac{\ln(2C)}{\ln2}\right)^2
\left[12\cdot22194000000\cdot G\left(\kappa\left(1+\frac{\ln(4d)}{\ln2}\right)+2\right)+32\right],$$

这里 $C=\operatorname{reserveSize}(c,\kappa)$、$d=\operatorname{digits}(c,\kappa)$，且

$$G=K\left[1+\left(\frac1{\ln2}+3\right)^\tau\right]+3,\qquad\tau=1-\varepsilon.$$

`GlobalSortingBound.rateConstant` 就是上式中的 $G$。`CommonLocalBudgetRate.K` 取三字记录对应的字段交换系数，即 `CommonSortingExchangeRate.rateConstant 3`。

## 字段交换系数继续展开

令 $q$ 为整个固定电路共用的素数，$m=512$，$W=24432543$。相关定义位于 [Swaps.lean](../Resources/Swaps.lean)、[Binary/Machine.lean](../../Interchange/Binary/Machine.lean) 和 [Fields/LogRate.lean](../../Interchange/Fields/LogRate.lean)。

`rateConstant r` 展开为

$$C_{\mathrm{machine}}\,r\,[1+((8m+2)\ln q)^\tau].$$

主定理取 $r=3$。其中

$$C_{\mathrm{machine}}=q^2 C_{\mathrm{fields}}+12+27q^2.$$

`C_fields` 是 `ArbitraryCostRate.finalConstant 24 27 (6*(2*q+6))`。若把这三个固定参数记为 $A,D,F$，则

$$C_{\mathrm{fields}}=
\left[2K_{\mathrm{rec}}m+A+2D+F\beta+20(\beta+1)\right]
\frac{m^\tau}{m^\tau-1}.$$

$\beta=\operatorname{borrowConstant}(q,W)=\lceil\log_{q^2}W\rceil$ 是移动高位数位所需的固定系数。$K_{\mathrm{rec}}$ 来自递归代价定理，见下一段。这些式子中没有 $N,M,B,w$、字段宽度、递归层数或输入值。

## 通过存在性定理选取的常数

[Recursion/Resources.lean](../../Interchange/Recursion/Resources.lean) 定义

```lean
def rateConstant : ℝ := Classical.choose exists_rate
```

关键在 `exists_rate` 的量词次序：它先给出一个 $K\ge0$，然后对**所有**块宽度 `b`、停止阈值 `cutoff`、递归层数 `k` 和数据量 `V` 证明相同的代价不等式：

$$\exists K\ge0,\ \forall b,\mathrm{cutoff},k,V,\quad
b>0\ \land\ Wb\le\mathrm{cutoff}\ \Longrightarrow\
Q(b,\mathrm{cutoff},k,V)\le K\left[1+\frac Vb m^{k\tau}\right].$$

`Classical.choose` 从这个存在性结论中固定选出一个满足要求的 $K$。这给出的是所有规模共用的系数。量词顺序及定义正文均保存在定义索引中。

## 内存阈值与磁盘指数

磁盘指数定义为

$$E=17+\left\lceil\log_2\operatorname{allowance}(u)\right\rceil.$$

`allowance` 取磁盘分配所需固定系数与控制编号所需固定系数的最大值；两个输入都只依赖固定构造和 $u$。继而 $d=c(E+1)$，`reserveSize` 用固定流数、$d$ 和固定比例要求计算预留系数 $C$，最后 $M_0=C^2$。

实际工作规模 $H=\lfloor M/C\rfloor$ 和逻辑块大小 $b=\max\{1,\lfloor B/C^2\rfloor\}$ 则随机器参数变化。这两个量作为参数传入算法；固定的是 $C$，并非 $H$ 或 $b$。

## 固定电路与素数

[Counts.lean](../../Circuit/Parameters/Counts.lean) 从数值 $111,439,63,512$ 计算流数 $W$ 和总边长 $S$；[Exponent.lean](../../Circuit/Parameters/Exponent.lean) 定义有理数 $\varepsilon=3/200000$。

[ExchangeSpecializationEndpoints.lean](../../Interchange/Bounds/ExchangeSpecializationEndpoints.lean) 先构造固定电路的有限有理矩阵族，再用 `specializeFamily` 选取保持这些矩阵关系的共同奇素数，最后将 `uniform.prime` 记为 `radix`。这个矩阵族及素数选择没有机器参数或输入数据作为参数。

## 与论文公式对应

`factor N M B` 展开后，代码中的实际传输次数 $Q$ 满足

$$Q\le C(c,\kappa)\frac NB\left[1+
\frac{\ln N}{(\ln(M/B))^{1-\varepsilon}(\ln M)^\varepsilon}\right].$$

分母指数之和为 1，因此统一改用以 2 为底的对数时，分子和分母的换底因子抵消。这就是论文定理 3.1 当前使用的公式；大 $O$ 省略的是上面已经逐层确定的固定系数。

返回[排序定理底层定义导航](Definitions.zh-CN.md)。
