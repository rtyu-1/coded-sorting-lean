# 编译与验证

[English](Verification.md) · [简体中文](Verification.zh-CN.md)

Lean 编译器检查各个定理的证明。项目的验证命令还会输出主定理及其使用的模型定义，检查声明是否与记录一致，并列出证明依赖的逻辑公理。一次完整运行的结果保存在 `lean/reports/`。

## 安装和运行

安装 [Lean 工具链管理器](https://lean-lang.org/install/)、Git 和 Python 3。下载仓库后进入 `lean/`，执行：

```sh
lake --version
lake exe cache get
python3 scripts/verify.py
```

`lean-toolchain` 选定 Lean 4.19.0，`lake-manifest.json` 固定 Mathlib 及其依赖版本。`lake exe cache get` 下载已编译的依赖，随后 `verify.py` 编译本项目的证明。首次构建包含规模较大的有限计算；后续构建会复用已完成的模块。

## 验证内容

1. 检查源码文件是否齐全，并运行 `lake build` 编译证明。
2. 输出主定理和选定的模型定义，与 `docs/model-baseline.json` 中记录的声明比较。
3. 运行比较程序的测试，确认它能识别定理或模型定义的变化。
4. 按数学主题输出定理使用的定义。
5. 从排序定理逐层提取项目定义，检查每条依赖都有对应条目，并编译底层指令、内存计数和复杂度公式的直接核对。
6. 检查对外主定理与实现定理的完整类型一致，并收集它们及其全部证明依赖所使用的公理。

公理检查覆盖排序定理、网络编码定理和有限块长编码结果。它接受本项目使用的三个逻辑原则：`propext` 将逻辑等价的命题视为相等，`Classical.choice` 从存在性证明中选取对象，`Quot.sound` 将等价关系用于商类型。

## 检查报告

| `reports/` 中的文件 | 内容 |
| --- | --- |
| `verification.json` | 检查结果、编译器版本、运行命令和源码哈希 |
| `build.log` | 编译器输出；构建失败时从末尾查找错误 |
| `review.md`、`review.zh-CN.md` | 按数学主题分组的 Lean 声明 |
| `axioms.log` | 主定理类型比较和公理依赖 |
| `model-snapshot.log` | Lean 输出的模型定义 |
| `definition-check.json`、`definition-closure.json` | 完整定义依赖及覆盖检查 |
| `definition-contracts.log` | 底层操作与资源公式的 Lean 核对 |

源码哈希用于标识报告对应的文件内容。[排序定理详解](SortingTheorem.zh-CN.md)集中说明论文定理 3.1 的条件、结论和计算模型与 Lean 声明及定义的对应关系，供读者人工核对；[模型说明](Model.zh-CN.md)概述排序与通信模型的约定。

## 单独运行检查

以下命令均在 `lean/` 中执行：

```sh
lake build
lake env lean ReviewEndpoints.lean
lake env lean ModelSnapshot.lean
lake env lean Audit.lean
```

文档修改使用 `python3 scripts/check_release.py` 检查链接、论文对应表、源码摘录和统计文件。`python3 scripts/source_inventory.py` 单独检查源码数量。

## GitHub Actions

[工作流配置](../../.github/workflows/lean.yml)在向 `main`、`public-release` 或 `public-release-*` 分支推送时运行，也检查以这些分支为目标的合并请求。工作流位于默认分支时，可以在 Actions 页面使用 **Run workflow** 手动启动。

自动验证在 `lean/` 目录执行文档检查、证明编译和定理检查，并将 `lean/reports/` 保存为可下载的报告。Actions 页面显示对应的提交、运行状态和报告入口。

## 编译资源

`lakefile.lean` 将 Lean 线程栈设为 32 MiB。Linux 自动验证使用两个 Lean 工作线程；本地可运行 `LEAN_NUM_THREADS=2 python3 scripts/verify.py` 采用相同设置。构建中断后，解决日志中的错误并重新执行，Lake 会复用已完成的模块。

独立 Linux 工具链可通过 `CODED_SORTING_TOOLCHAIN` 指定目录，再运行 `python3 scripts/verify.py --builder parallel --jobs 2`。该编译方式记录各模块的源码、导入模块、编译器和选项，用于判断已完成结果能否复用。[编译工具](../scripts/README.zh-CN.md)列出了相关辅助命令。
