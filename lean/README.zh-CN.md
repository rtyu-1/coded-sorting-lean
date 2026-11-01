# Lean 证明项目

[English](README.md) · [简体中文](README.zh-CN.md)

本目录包含外存整数排序和无向多单播网络编码的完整 Lean 证明。源码从有限电路出发，构造程序和网络，再证明各自的正确性、复杂度和容量结论。

## 编译

安装 Lean 工具链管理器和 Python 3 后，在本目录执行：

```sh
lake exe cache get
python3 scripts/verify.py
```

`lean-toolchain` 和 `lake-manifest.json` 固定编译器与依赖版本。完整的安装、运行和报告说明见[编译与验证](docs/Verification.zh-CN.md)。

## 代码入口

| 文件 | 内容 |
| --- | --- |
| [CodedSorting.lean](CodedSorting.lean) | 导入论文中的主要结果 |
| [定理 3.1](CodedSorting/Sorting/Theorem31/Theorem.lean) | 整数排序正确性和复杂度 |
| [定理 3.2](CodedSorting/NetworkCoding/Theorem32/Theorem.lean) | 同一网络上的编码和路由容量 |

在装有 Lean 4 扩展的 VS Code 中打开本目录，可以随光标位置查看定义的类型和证明状态。[阅读指南](docs/README.zh-CN.md)介绍数学内容，[源码结构](docs/Structure.zh-CN.md)介绍目录组织。
