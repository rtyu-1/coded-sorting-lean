# 字、数组与地址的含义

磁盘和内存里的值最终都需要用有限个比特表示。这里把一个字定义成有范围限制的自然数，再用固定长度的函数表示一排存储位置。

## 一个字和一排字

[WordConvention.lean](WordConvention.lean) 中的 `Word w` 是 `Fin (2^w)`：一个自然数 `val`，连同 `val < 2^w` 的证明。证明用于检查范围；机器保存的是这个 $w$ 位自然数。

`Words d w` 是 `Fin d → Word w`。下标取 $0,\ldots,d-1$，每个下标对应一个字，因此它表示恰好 $d$ 个字。函数写法描述各位置的内容；位置数量由 `d` 决定。

`WordConvention.Covers N w c` 展开为 `Nat.clog 2 N ≤ c*w`，即 $\lceil\log_2N\rceil\le cw$。顶层还要求 $w\ln2\le\kappa\ln N$。固定 $c,\kappa$ 后，两式共同表达 $w=\Theta(\log N)$。

## 地址怎样放进若干个字

`decodeWords` 使用基础库的 `finFunctionFinEquiv`，将 $d$ 个 $w$ 位字与范围 $0,\ldots,(2^w)^d-1$ 内的自然数一一对应。`encodeNat` 和 `counterCode` 做反向分解。编码函数对超过容量的自然数取模，使函数对所有参数都有定义；运行中实际使用的地址和计数器值另有范围证明，保证它们小于 $(2^w)^d$，此时编码后再解码得到原值。

若磁盘规模由 $N^E$ 界定，代码取 $d=c(E+1)$。由 $\lceil\log_2N\rceil\le cw$ 可得 $N^{E+1}\le (2^w)^d$。这解释了为什么地址需要固定数量的字：$c$ 和 $E$ 固定，而地址的数值可以随 $N$ 增长。

`Fin R ⊕ (Fin R ⊕ Fin R)` 表示三个互不重叠的地址区，每区 $R$ 个块，共 $3R$ 个块。选择哪个区和区内偏移一起编码；[内存布局说明](../../Sorting/Resources/Definitions.zh-CN.md)列出了为完整地址预留的字数。

## 读一个输入整数

[PhysicalHalted.lean](../../Sorting/Execution/Framework/PhysicalHalted.lean) 的 `inputWord q disk i` 从第 $\lfloor i/B\rfloor$ 个物理块、第 $i\bmod B$ 个字取值。`InputFile q disk xs` 要求每个合法下标处读到的值等于 `xs` 中对应元素。

这里的 `xs` 是描述输入内容的数学列表。执行程序从 `disk` 读数据；程序表达式由规模参数确定，在声明“对任意 `disk,xs` 都成立”之前就已经确定。

## 读到基础层时

`Fin` 是带上界的自然数，`→` 是函数，`⊕` 是带左右标记的二选一，`List` 是有限列表，`%` 和 `/` 分别是余数与自然数除法。它们在这里分别表达值域、存储位置、磁盘区、输入序列和地址分解。

返回[排序定理底层定义导航](../../Sorting/Theorem31/Definitions.zh-CN.md)。
