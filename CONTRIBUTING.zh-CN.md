# 参与贡献

[English](CONTRIBUTING.md) · [简体中文](CONTRIBUTING.zh-CN.md)

贡献可以是改进证明、澄清数学定义、解释构造思路或简化编译流程。修改说明应让首次看到这项改动的读者理解它的内容和用途。

## 开发环境

使用 `lean/lean-toolchain` 指定的 Lean 版本和 `lean/lake-manifest.json` 中的依赖。在支持 Lean 的编辑器中打开 `lean/`，以下命令均在该目录执行。安装步骤见[编译与验证](lean/docs/Verification.zh-CN.md)。

## 修改证明

在对应的 `CodedSorting` 模块中修改代码。数学陈述或阅读顺序发生变化时，同步更新该模块的导读，然后运行：

```sh
python3 scripts/verify.py
```

该命令编译证明，并将定理声明、模型定义和公理依赖保存到 `reports/`。合并请求应说明数学内容的变化，并附上验证命令及结果。

## 修改文档

从问题和构造目的开始介绍，再展开技术细节。首次出现的概念应有解释，并链接到对应源码。中英文页面保持一致，正文应能独立阅读。自动生成的页面通过生成脚本修改。

修改后运行：

```sh
python3 scripts/check_release.py
```

该命令检查本地链接、论文对应表、源码摘录和统计文件。

## 修改模型定义

`ModelSnapshot.lean` 输出选定的定理和定义，验证脚本将它们与 `docs/model-baseline.json` 比较。需要调整模型时，在中英文模型说明中解释新定义，更新 `docs/statement-correspondence.json` 中的源码引用，检查新输出后再更新记录，最后重新运行完整验证。

## 报告问题

提供文件路径、声明名、相关数学陈述或命令，以及复现步骤。编译问题还应附上 Lean 版本和 `reports/build.log` 末尾的错误信息。
