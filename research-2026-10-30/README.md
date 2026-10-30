# 2026-10-29 至 10-30 轮的原始材料

这一轮的总结与未来路线见 [交接记录](../docs/HANDOFF_2026-10-30.md)。本目录保存这一轮的原始推导、程序、日志与数据。

首次归档后只做过两类后续修改（2026-10-30 晚间），改动都可以在 git 历史里看到：
- **增补：** ROUTE_Q_zh.md 增补第 12.7 节（审查更正）和第 13 节（M1 结果），并新增 exp16 系列程序。
- **修正：**
  - exp15_phi2first.py 按 Codex 审查做了修正：原来的 `free_lit` 方向错误，使先清后移的约束失效。
  - 第 13 节按第二条 Codex 审查做了修正：slack 判据只是贪心收尾的充分条件，原文误写成等价（第 13.6 节）。
  - exp16_nibble.py 只改了注释，并把 `fail` 表达式抽成函数 `certificate_fails`，输出不变；新增回归测试 test_exp16_criteria.py。
- **增补（大围长）：** 新增 LARGE_GIRTH_zh.md、exp18_large_girth.py 和 exp18.log。

- [LARGE_GIRTH_zh.md](LARGE_GIRTH_zh.md)：**大围长情形已解决。** 用匹配收缩加 Kostochka 定理证明：第一类图围长 ≥ 41、一般图围长 ≥ 39360 时，χ'_s ≤ 20。
- [ROUTE_Q_zh.md](ROUTE_Q_zh.md)：主推导，第 1–12 节。
- [REPORT_zh.md](REPORT_zh.md)：这一轮开头的文献核查、早期发现与路线提案。

## 环境

需要 Python 3.12 以上，以及 `python-sat`、`networkx`、`numpy`。在本目录下运行各个程序。论文全文没有收录，编号见交接记录第 2 节。

## 程序

| 文件 | 内容 | 结果与对应章节 |
|---|---|---|
| [sec.py](sec.py) | 公共工具：强冲突图、SAT 染色、2 因子分解 | — |
| [exp1_factor_chi.py](exp1_factor_chi.py)、[exp2_c11.py](exp2_c11.py) | 2 因子 F 的 χ(H_F) | 发现 A（REPORT 第 3 节） |
| [exp3_pairs.py](exp3_pairs.py) | 性质 Q 的 SAT 检验 | 550 个图全部满足 Q |
| [exp4_local_search.py](exp4_local_search.py)、[exp4b_stats.py](exp4b_stats.py) | Lovász 式局部搜索 | REPORT 第 5 节 |
| [exp5_bootstrap.py](exp5_bootstrap.py)、[exp5b_high_girth.py](exp5b_high_girth.py) | 贪心序障碍（bootstrap 渗流） | 发现 B（REPORT 第 4 节） |
| [exp6_hard_search.py](exp6_hard_search.py) | 爬山搜索 χ'_s 大的图 | 只找到 χ'_s ≤ 17 的图 |
| [exp7_stuck.py](exp7_stuck.py)、[graphs_hg.py](graphs_hg.py) | 真实高围长图上的卡死搜索 | 30/30 不卡死（ROUTE_Q 第 3.1 节） |
| [exp8_local_sat.py](exp8_local_sat.py)、[exp8b_witness.py](exp8b_witness.py) | 通用局部模型（4 正则树球） | SAT（ROUTE_Q 第 3.2 节） |
| [exp9_potentials.py](exp9_potentials.py)、[exp9b_hub.py](exp9b_hub.py)、[exp9c_witness.py](exp9c_witness.py)、[exp9d_spread.py](exp9d_spread.py) | 加强的势函数，三角形 | 引理 7、9（ROUTE_Q 第 6–7 节） |
| [exp10_enum.py](exp10_enum.py)、[exp10_testQ.py](exp10_testQ.py) | 枚举 n ≤ 13 的连通 4 正则图并检验 Q | 全部满足 Q（ROUTE_Q 第 8 节） |
| [exp10c_dense.py](exp10c_dense.py)、[exp10d_slack.py](exp10d_slack.py)、[exp10e_dense9.py](exp10e_dense9.py) | 稠密图，9 对版本 | ROUTE_Q 第 8.3 节 |
| [exp11_pairing.py](exp11_pairing.py) | 扇形论证：路只有两个端点 | SAT（ROUTE_Q 第 9 节） |
| [exp12_closure_tree.py](exp12_closure_tree.py) | 引理 11 的闭合树，深度 1 和 2 | SAT（ROUTE_Q 第 9 节） |
| [exp13_brooks.py](exp13_brooks.py)、[exp13b_witness.py](exp13b_witness.py) | Brooks 型划分，引理 A、B | ROUTE_Q 第 10 节 |
| [exp14_periodic.py](exp14_periodic.py) | 周期性卡死路测试 | 奇数周期 3 可满足（ROUTE_Q 第 11 节） |
| [exp15_phi2first.py](exp15_phi2first.py)、[exp15b_witness.py](exp15b_witness.py) | 势函数换序 (Φ₂, Φ₁)，绕行，先清后移 | 修正后周期 3 仍 SAT（ROUTE_Q 第 12、12.7 节） |
| [exp16_nibble.py](exp16_nibble.py) | M1：多轮 nibble 加贪心收尾；判据失败概率（充分判据 \|L\| ≤ U 不成立）与局部引理阈值的比较 | ROUTE_Q 第 13 节 |
| [exp16b_decay.py](exp16b_decay.py) | 判据失败概率随轮数的衰减（每个 T 取 6×10⁶ 个样本） | 每轮约 ×7–40，而依赖度每轮 ×6561；只说明这一判据下局部引理闭合不了 |
| [test_exp16_criteria.py](test_exp16_criteria.py) | 回归测试：区分判据失败、`greedy_finish` 失败、剩余部分确实不可染，含 Codex 反例；并检验"存在成功顺序"与"可染"等价 | 6/6 通过（ROUTE_Q 第 13.6 节） |
| [exp16c_repair.py](exp16c_repair.py) | 列表为空的卡死边能否一步修复 | T = 3–5 中没有出现空列表的边 |
| [exp16d_leftover.py](exp16d_leftover.py) | 剩余分支的精确列表染色 | T = 3–6 全部可染 |
| [exp18_large_girth.py](exp18_large_girth.py) | 逐步执行大围长定理 B 的构造，检查每条结构断言，并验证最终的 20 色强边染色 | 10/12 通过；另 2 个是测试围长太小时贪心选不出 D。按 Codex 审查修正了哑点弧未删的错误（LARGE_GIRTH 第 5 节，[exp18.log](exp18.log)） |
| [exp19_property_m.py](exp19_property_m.py) | 性质 M（至多 4 或 5 个匹配，Σχ(H(M_i)) ≤ 20）：模式 small 检验 n ≤ 13 的全部图，exact 用枚举求精确预算，slack 测中等围长的余量；tight 模式已弃用（不可满足的证明太慢） | 12672 个图全部满足；恰好需要 20 的有 3 个（LARGE_GIRTH 第 8 节，[small](exp19_small.log)、[exact](exp19_exact.log)、[slack](exp19_slack.log)） |
| [exp19b_families.py](exp19b_families.py) | 性质 M 在 C_k[2]、C_n(1,2)、C_n(1,3) 上的检验（n ≤ 20） | 全部满足，只有 C5[2] 恰好需要 20（[exp19b.log](exp19b.log)） |
| [run9.sh](run9.sh) | exp9 的批量运行脚本 | — |

## 数据与日志

- `graphs_n5.txt` 到 `graphs_n13.txt`：exp10_enum.py 枚举出的连通 4 正则图，每行一个图，计数与 OEIS A006820 吻合。
- `exp1_results.json`、`exp7_results.json`，以及 `exp1.log`、`exp6.log`、`exp7.log`、`logs_enum.log`：对应程序的输出。
- `hg_n1000_g7_s1.edges`：exp16 使用的 n = 1000、围长 7 的随机 4 正则图（边表）。
- `logs15fix`：exp15 修正后的重跑日志。`logs15` 中含 `cmp` 的结果因编码错误作废。
- `logs9` 到 `logs15`：各轮 SAT 运行的日志，文件名标出了参数。
  - **作废：** `logs13/k12_T.log` 中深度 1 的远记号结果，原因是守卫覆盖错误，见交接记录第 5 节。
  - **不完整：** `logs9` 中的空日志来自被终止的旧运行，`logs13/k12_B.log` 只含深度 0 的结果。
