# 程序与证书复现说明

## 本次归档检查的范围

归档阶段只检查文件是否齐全、字节校验值是否一致、JSON是否可解析、Python是否可语法解析，以及新整理文档的本地链接是否存在。没有重新启动研究目标，也没有把静态检查写成数学验证。

所有原始脚本、输出和研究稿都保留在 `research/`。脚本并非统一测试框架；有的是搜索器，有的是生成器，有的是读已有证书的验证器。部分程序会覆盖同名JSON，重新运行前应保留快照或使用另一个Git工作副本。

## 环境

原执行环境为Windows、PowerShell、Python 3.12。脚本主体使用Python标准库，少数脚本从同目录导入其他研究脚本；因此保持 `research/` 内相对位置，或从仓库根目录按下列方式执行。无需依据原检查点里的本机绝对路径寻找运行时。

```bash
python --version
python research/check_certificates.py
```

大整数、多项式系数、回溯和图验证均在普通Python整数与集合上运行。某些枚举族可能较慢；本档案不附统一运行时间保证。

两个早期探索脚本 `factor_partition_k4.py`、`factor_partition_tower.py` 另外导入NumPy；复跑它们需自行安装NumPy，原版本未锁定。其余静态发现的 `research.*` 导入是本仓库自身模块。对使用这些导入的程序，应从仓库根目录以 `python -m research.模块名` 运行；例如 `python -m research.high_conflict_types`。不要把可选实验的NumPy依赖误当作归档检查工具或全部纯Python证书的依赖。

## 只检查档案

```bash
python tools/package_archive.py verify
```

该工具不会导入或运行 `research/*.py`。它检查：

- 315个原始研究文件与原始快照清单逐字节一致。
- 仓库归档文件与 `archive/MANIFEST.json` 相符。
- JSON可解析，Python可用AST解析。
- 根README及 `docs/` 内本地Markdown链接指向存在的文件。

`archive/packaging_check.json` 保存本次归档检查报告。校验清单本身及该检查报告不列入全仓库自校验，避免循环依赖；原始研究快照清单则列入。

## 代表性数学证书入口

下表说明现有程序的用途，供用户未来主动复现，不表示归档时重新执行了这些数学检查。

| 项目 | 入口与依赖 | 能核查的范围 |
|---|---|---|
| 454个图的908份色表 | `python research/check_certificates.py`；读取colouring_certificates.json | 直接按原题端点定义核对保存色表，不证明全部图 |
| 1362个诱导匹配证书 | `python research/packing_verify.py`；读取colouring_certificates.json和packing_certificates.json | 检查两两不冲突及样本中的20倍规模不等式 |
| Petersen删边系数 | `petersen_minus_polynomial.py`、`petersen_minus_verify.py`、`petersen_minus_independent.py` | 三种精确整数计算；普遍列表结论仍需配合证明稿 |
| 16团边界有限模型 | `high_conflict_types.py`、`clique16_boundary_search.py` | 指定有限类型及补边空间，范围见各自证明稿 |
| 三、四重覆盖 | `factor_triple_permutation_lifts.py`、`factor_cyclic_lift_search.py`、`factor_cover_independent_audit.py` | 指定基图和覆盖阶数的完整范围，非任意覆盖 |
| 十三点五临界核 | `joint_thirteen_probe.py` | 显式边表、不可四色搜索、逐删点四色表 |
| 十三点核的完整原图实现 | `joint_thirteen_realization.py`之后`joint_thirteen_realization_verify.py` | 2020点正规图及选定冲突核；无最优分区 |
| C7双吹胀原图实现 | `joint_c7_cover.py`之后`joint_c7_cover_verify.py` | 2121点、完整二因子、围长与指定冲突图 |
| 指定递归临界核族 | `joint_gadget_tree_family.py`和`joint_gadget_sequence_verify.py` | 两种独立生成视角的有界递归族 |
| 541临界规模整数表 | `python research/factor_541_bound_check.py` | 仅核算最终29/29/32参数表，不枚举图 |
| 局部颜色等价 | `python research/hanger_local_reductions_check.py` | 三边路及C5/三角替换的各27种外颜色 |
| 小部K4五邻失败O9核 | `python research/small_clique_insertion_obstruction.py` | 显式局部核及9522点正规补全 |
| 非邻双高五色核 | `python research/five_critical_two_nonadjacent_endpoint.py` | 20点原端点、9点临界核、逐删点色表；有限补全由纯引理保证 |
| 平衡停止核局部搜索 | `python research/small_clique_balanced_gate_search.py` | 明确fresh模型和单跨外边模型，版本范围见历史JSON |

对于“生成后再核验”的项目，先等生成器完成，再启动读取其输出的核验器。程序终止或覆盖输出不清楚时，不要把旧JSON误认为新运行结果。

## 原端点证书的判断标准

一个完整实现证书需要分别核查原图简单性、原最大度或四正则性、围长、红边是否真是完整二因子，以及选定红边之间的冲突是否逐对等于声称的核。只给冲突图的抽象边表，不足以证明它能来自目标原图。

即使这五项全部通过，也没有自动核查A/B/C为全局最小势。要求最优分区的反例还需另外给出该最优性证明或证书。档案中的局部实现没有混称为原问题反例。

## 失败或结果不一致时

先核对脚本与JSON的校验值和版本，再核对输入、随机种子、范围及生成顺序。不要仅依赖搜索节点数；证书里的图和着色通常可以用独立端点程序直接验证。

原始脚本输出格式各异，完整索引见 [文件索引](FILE_INDEX.md)。历史更正在 [审核记录](AUDIT_AND_CORRECTIONS.md)，暂停前未完成的新公式在 [交接笔记](PAUSED_HANDOFF.md)。
