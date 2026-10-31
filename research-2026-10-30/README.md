# 2026-10-29 至 10-30 轮的原始材料

这一轮的总结与未来路线见 [交接记录](../docs/HANDOFF_2026-10-30.md)。本目录保存这一轮的原始推导、程序、日志与数据。

首次归档后只做过两类后续修改（2026-10-30 晚间），改动都可以在 git 历史里看到：
- **增补：** ROUTE_Q_zh.md 增补第 12.7 节（审查更正）和第 13 节（M1 结果），并新增 exp16 系列程序。
- **修正：**
  - exp15_phi2first.py 按 Codex 审查做了修正：原来的 `free_lit` 方向错误，使先清后移的约束失效。
  - 第 13 节按第二条 Codex 审查做了修正：slack 判据只是贪心收尾的充分条件，原文误写成等价（第 13.6 节）。
  - exp16_nibble.py 只改了注释，并把 `fail` 表达式抽成函数 `certificate_fails`，输出不变；新增回归测试 test_exp16_criteria.py。
- **增补（大围长）：** 新增 LARGE_GIRTH_zh.md、exp18_large_girth.py 和 exp18.log。其后又陆续新增 exp19–exp31 及其日志（性质 M、P、R；2026-11-01 的九类方案检验），见下表。

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
| [exp20_search.py](exp20_search.py) | n = 14–20 的爬山：最大化 4 匹配形式的精确预算 B*（遍历全部 1-因子分解） | 48 次，约 144 万步，B* ≤ 20，没有反例（LARGE_GIRTH 第 8.1 节，[exp20.log](exp20.log)、[exp20b.log](exp20b.log)） |
| [exp20c_glue.py](exp20c_glue.py) | 把紧图两两沿 2 边割粘接，再求 B* | 754 个图（n = 20–28）全部 ≤ 20（[exp20c.log](exp20c.log)） |
| [exp21_property_p.py](exp21_property_p.py) | 性质 P（5 边染色中，每条颜色为 c 的边至多 5 个外邻点被颜色 c 覆盖；配合定理 B'，围长 ≥ 69 ⇒ 20 色）：small 和 girth 模式检验小图，random 模式检验随机图 | 165 个小图失败，全部围长 ≤ 4；围长 5–7 的 20 个随机图全部满足（LARGE_GIRTH 第 9 节，[small](exp21_small.log)、[girth](exp21_girth.log)、[random](exp21_random.log)） |
| [exp22_kempe.py](exp22_kempe.py) | 性质 P 的 Kempe 局部搜索：单步或两步下降、平移步；ball 模式重染半径 1–4 的球；sanity 模式检验重染求解器 | 下降总会卡住；卡住的边在半径 ≤ 4 内被证明不可修复（LARGE_GIRTH 第 9.6 节，[exp22.log](exp22.log)） |
| [exp23_structured.py](exp23_structured.py) | 结构化构造（F₁ 用 {1,2,5}，F₂ 用 {3,4,5}）：V1 见证点不限，V2 只沿自身所在的圈；families 模式拆开各约束族 | V1 全部可满足，V2 全部不可满足（计数引理：要求所有圈长都是 5 的倍数）（[exp23.log](exp23.log)） |
| [exp24_property_r.py](exp24_property_r.py) | 性质 R（一个色类是诱导匹配、一个色类 Δ(H(K)) ≤ 5，其余不限；定理 B 构造的就是它，围长 ≥ 69 ⇒ 20 色）：small、random、compare 模式检验性质 R（compare 与性质 P 对照）；fixedD、dead、resample、core 模式在奇圈最密的图上检验定理 B 流程；tree 模式在 4 正则树的球上检验 | 小图 12669/12672 满足（P 为 12507）；随机第二类图全部满足；缺陷集稠密时定理 B 流程因"死边"失败；树上距离 5 时 40/40 成功、距离 4 有反例（LARGE_GIRTH 第 10 节，[small](exp24_small.log)、[random](exp24_random.log)、[compare](exp24_compare.log)、[dense](exp24_dense.log)、[tree](exp24_tree.log)） |
| [exp25_dead_girth8.py](exp25_dead_girth8.py) | 引理 5 第二种情形在围长 8 时的反例：围长恰为 8、u 和 v 都不是缺陷端点、uv 是死边，只用 4 条缺陷边（2026-10-31 审查发现） | 确认；引理 5(b) 需要围长 ≥ 9（[日志](exp25.log)，LARGE_GIRTH 第 10.8 节） |
| [exp26_triangle_lock.py](exp26_triangle_lock.py) | 九类方案的类内三角形：在 4 正则树的球上用 SAT 判定，在 (Φ₁, #类内三角形) 的字典序最小者中，单个类内三角形能否锁住、两个锁住的三角形能否互相冲突。模式有 single、pair、pairorb、pairpar，可加翻转条件 | 可满足：锁住的单个三角形、互相冲突的锁住三角形对都能在局部出现，包括 9 对边全冲突的一对；加翻转条件后，完成的 47/111 个轨道也全部可满足（NEW_DIRECTIONS 第 9.1 节；日志：[单个](exp26_single4.log)、[成对](exp26_pair5.log)、[成对加翻转](exp26_pair5_flip.log)） |
| [exp27_q9_n14.py](exp27_q9_n14.py) | 用并行的双边交换 BFS 枚举 n = 14 的全部连通 4 正则图，再检验猜想 Q₉（9 个二部类，即 18 色）；complete 模式用精确同构判定补上哈希判重漏掉的类 | 88168 个类（与 A006820 一致，BFS 漏的 2 个由 complete 模式补上），全部满足 Q₉（NEW_DIRECTIONS 第 9.6 节，[日志](exp27_n14.log)） |
| [exp28_q9_large.py](exp28_q9_large.py) | 大图（n = 2000–5000，围长 5–10）上 9 类、8 类的 Lovász 下降和记号搜索 | 9 类：下降后至多 1 个三角形，一步消掉；8 类：三角形全部可以消掉，2 次留下度为 3 的边（NEW_DIRECTIONS 第 9.2 节，[日志](exp28.log)） |
| [exp29_local_rounds.py](exp29_local_rounds.py) | 有界轮数的同步局部下降，记录每轮的坏边比例 | 每轮只降 ×1.5–2.3，坏边扎堆，局部引理走不通（NEW_DIRECTIONS 第 9.3 节，[日志](exp29.log)） |
| [exp30_brooks8.py](exp30_brooks8.py) | L² 能否分成 k 类、每类最大度 ≤ 2（k = 8、7） | n ≤ 14 全部存在（n = 14 共 88168 个）；随机图 n = 500、1000 上连 6 类也存在（NEW_DIRECTIONS 第 9.4 节，[k = 8](exp30_k8.log)、[k = 7](exp30_k7.log)、[随机图](exp30_random.log)） |
| [exp31_lll_girth.py](exp31_lll_girth.py) | 定理 3.14：用局部引理选缺陷集 D，排除距离 ≤ 4 的对和沿测地线成串的缺陷边；42 状态转移矩阵计数，brute 模式与直接枚举对照，cert 模式用十进制向上舍入严格检验 | g = 5710 时条件成立，无条件门槛 39360 → 5710（手稿第 3.7' 节，[日志](exp31.log)） |
| [run9.sh](run9.sh) | exp9 的批量运行脚本 | — |

## 数据与日志

- `graphs_n5.txt` 到 `graphs_n13.txt`：exp10_enum.py 枚举出的连通 4 正则图，每行一个图，计数与 OEIS A006820 吻合。
- `exp1_results.json`、`exp7_results.json`，以及 `exp1.log`、`exp6.log`、`exp7.log`、`logs_enum.log`：对应程序的输出。
- `hg_n1000_g7_s1.edges`：exp16 使用的 n = 1000、围长 7 的随机 4 正则图（边表）。
- `logs15fix`：exp15 修正后的重跑日志。`logs15` 中含 `cmp` 的结果因编码错误作废。
- `logs9` 到 `logs15`：各轮 SAT 运行的日志，文件名标出了参数。
  - **作废：** `logs13/k12_T.log` 中深度 1 的远记号结果，原因是守卫覆盖错误，见交接记录第 5 节。
  - **不完整：** `logs9` 中的空日志来自被终止的旧运行，`logs13/k12_B.log` 只含深度 0 的结果。
