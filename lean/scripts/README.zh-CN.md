# 编译工具

[English](README.md) · [简体中文](README.zh-CN.md)

`verify.py` 是完整验证的入口，负责编译证明、检查主定理与模型定义，并保存报告。下面的辅助工具分别处理文档、源码统计和构建环境。所有命令都从 `lean/` 目录运行。

## 常用命令

| 工具 | 作用 |
| --- | --- |
| `verify.py` | 编译证明，检查定理类型、模型定义和公理依赖 |
| `check_release.py` | 检查文档链接、论文对应表、源码摘录及导入文件是否齐全 |
| `source_inventory.py` | 检查模块数与行数；`--write` 更新统计文件 |
| `check_model_baseline.py` | 比较 Lean 打印的定义与记录的版本 |
| `test_model_baseline.py` | 测试定义比较程序能否识别变化 |

## 独立工具链

以下工具用于直接调用指定的 Linux Lean 工具链。运行方式见[编译与验证](../docs/Verification.zh-CN.md)。

| 工具 | 作用 |
| --- | --- |
| `compile_parallel_modules.py` | 控制同时编译的模块数，并复用已完成结果 |
| `run_lean_tool.py` | 调用指定的 Lean 或 Lake 程序 |
| `restore_pinned_packages.py` | 按 Lake 清单恢复依赖版本 |
| `fetch_missing_mathlib.py` | 下载缺失的 Mathlib 编译模块 |

本目录中的 `.lean` 和 `.c` 文件支持这些独立工具链命令。
