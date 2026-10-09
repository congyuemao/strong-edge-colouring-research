# 成果与证据登记表

登记截止：2026-10-09。所有条目都以所列条件为限。这里的“证明”指有完整证明稿并有研究内复核记录；“计算辅助”表示普遍结论还依赖覆盖明确的有限验证；“有限计算”不能推出一般结论。该表不宣称外部同行审稿或形式化验证完成。

## 一般二十色问题

| 编号 | 已得结论或证据 | 类型及边界 | 主要文件 |
|---|---|---|---|
| G01 | 五圈双点吹胀需二十色；所有最大度四图独立得二十二色 | 证明；前者下界最佳候选，后者历史弱界 | [下界](../research/counterexamples.md)、[22界](../research/bound22.md) |
| G02 | 二十边强团只能为孤立的五圈双点吹胀紧分量 | 证明 | [等号分类](../research/clique20_rigidity.md) |
| G03 | 任意 F 有 `|F|≤20ν_s(F)`，并有局部多项式算法 | 证明及1362份有限证书；不等于二十色 | [定理](../research/packing_private_cliques.md)、[独立检查器](../research/packing_verify.py) |
| G04 | `2|F|≤39ν_s(F)+t`，t计完整紧二十分量 | 证明；未证明19.5常数最佳 | [第8节](../research/packing_private_cliques.md)、[20/21阈值](../research/high_conflict_20_21_improved.md)、[22阈值](../research/high_conflict_22_improved.md)、[23阈值](../research/high_conflict_23_improved.md) |
| G05 | 至多41条原边可二十色；21临界边集至少42条边 | 证明链 | [规模](../research/critical_size_continuation.md)、[补图分解](../research/critical_complement_connectivity.md)、[无三角分支](../research/dense_complement41.md)、[有三角分支](../research/critical41_triangles.md) |
| G06 | 任意41条原边存在三条两两不冲突边 | 证明；独立数保证不等于整体染色 | [稠密补图](../research/dense_complement41.md) |
| G07 | 21临界冲突子图强团至多15 | 计算辅助必要条件 | [16团模型](../research/clique16_boundary_model.md)、[边界结果](../research/clique16_boundary_result.json)、[高冲突类型](../research/high_conflict_types.py) |
| G08 | 原冲突度均24的强团至多7 | 证明 | [临界支撑](../research/critical_support.md) |
| G09 | 临界边集不含原三角形边 | 证明；不能据此删除整个三角形顶点集 | [三角可约](../research/triangle_reducibility.md) |
| G10 | 支撑内非候选连接分量只取有限路径、爪类或三角形 | 证明 | [连接边](../research/noncritical_connectors.md) |
| G11 | 紧点外端独立、缺额预算及度三点距离限制 | 证明 | [紧点](../research/tight_endpoint_interactions.md)、[缺额](../research/critical_defect_budget.md) |
| G12 | 极小原反例3点连通、非平凡割至少5；4正则时至少6 | 证明；不表示反例存在 | [全局条件](../research/global_continuation.md)、[五匹配割拼合](../research/cut5_matching.md) |
| G13 | K3,3块及关联边可从任意外部部分二十染色延拓 | 证明及100个紧边界验证 | [证明](../research/k33_reducibility.md)、[程序](../research/k33_extension_check.py) |
| G14 | Petersen块的八列表接口及相应可约性 | 证明，注意诱导及围长条件 | [证明](../research/petersen_reducibility.md) |
| G15 | Petersen删边14边的5/7/8列表可染，多项式系数12240 | 计算辅助列表定理，三份整数程序一致 | [证明](../research/petersen_minus_reducibility.md)、[生成](../research/petersen_minus_polynomial.py)、[核验](../research/petersen_minus_verify.py)、[独立计算](../research/petersen_minus_independent.py) |
| G16 | 对应临界支撑的匹配冲突K4不能共三角形 | 证明，使用Petersen删边可约块 | [交叠](../research/matching_k4_overlap.md) |

## 高围长与二因子

| 编号 | 已得结论或证据 | 类型及边界 | 主要文件 |
|---|---|---|---|
| F01 | 围长≥5强团≤7；候选F度≤2强团≤5 | 独立证明；7已有文献先例，5文献地位未确认 | [证明所在稿](../research/high_girth_fractional.md)、[文献核查](../research/high_girth_clique_literature.md) |
| F02 | 分数≤16及≤9为现基准；旧加权19及10不再算突破 | 用户更新基准；非整数结论 | [旧独立稿及范围](../research/high_girth_fractional.md)、[原总览](../research/README.md) |
| F03 | Δ≤12、ω≤5、n≤22可十色，n≤19可九色 | 证明；因子反例至少23原点 | [小阶](../research/factor_small_order.md) |
| F04 | Z11因子基图的任意高围长置换覆盖十色 | 证明；完整覆盖族而非任意G | [任意阶覆盖](../research/factor_cover_all_orders.md) |
| F05 | 六圈双点基图的任意高围长覆盖十色 | 证明 | [K12覆盖分类第5节](../research/factor_k12_cover_classification.md) |
| F06 | 二重覆盖无合格例；三重置换6个；四重循环8184个均≤9色 | 有限穷举与独立集合/色表复核 | [搜索范围](../research/factor_cover_search.md)、[独立审计](../research/factor_cover_independent_audit.md) |
| F07 | 红五圈蓝匹配圈链至多七色，精确5/6/7分类 | 证明及84份色表 | [五圈链](../research/factor_c5_cycle_layers.md)、[检查](../research/factor_c5_cycle_layers_check.py) |
| F08 | 不能(5,5)度分区的无限族实际仅需六色 | 方法反例，不是十色反例 | [度分区障碍](../research/factor_half_degree_obstruction.md)、[精确六色](../research/factor_odd_layer_six.md) |
| F09 | 五边强团仅C5及四种森林形；精确交叠和私有胶合 | 证明与局部枚举复核 | [几何分类](../research/factor_five_clique_geometry.md)、[核查程序](../research/factor_five_clique_geometry_check.py) |
| F10 | (4,3,3)分区同点同小部饱和转移至多二 | 证明；不是全转移网络度≤2 | [总界](../research/factor_saturated_private_bound.md)、[三分支之一](../research/factor_three_saturated_dd41.md)、[全r](../research/three_saturated_cross.md)、[单对角](../research/three_saturated_single_diagonal.md) |
| F11 | 五级最优中匹配坏团每点同小部至多一饱和邻；双饱和剩挂边类 | 证明 | [双饱和](../research/factor_two_saturated.md) |
| F12 | 全硬五圈挂边类任意多块同步修复 | 证明；其他坏团、小部K4未覆盖 | [第14—15节](../research/factor_two_saturated.md) |
| F13 | 红C5坏团向两小部各有单点出口；关联单圈等条件下同步 | 条件性证明 | [分区交换第3、5节](../research/factor_partition_exchange.md) |
| F14 | 原小部K4存在A≥5且不接实际坏A-K5的点 | 证明；点不自动可插入 | [K4出口](../research/factor_small_clique_routes.md) |
| F15 | 固定A六邻闭包可六染；A四邻零转移及C5平衡停止核排除 | 证明，未闭合所有转移链 | [第6、8节](../research/factor_small_clique_routes.md) |
| F16 | A五邻候选可失败，O9局部核有9522点正规实现 | 有限明确构造，无全局最优分区 | [程序/证书](../research/small_clique_insertion_obstruction.py) |
| F17 | 平衡停止核局部搜索版本更正；跨一外边匹配型20/20局部可行 | 有限计算；纯fresh阴性不能外推 | [历史](../research/small_clique_balanced_gate_search_history.json)、[程序](../research/small_clique_balanced_gate_search.py) |

## 围长六的奇圈与匹配同步

| 编号 | 已得结论或证据 | 类型及边界 | 主要文件 |
|---|---|---|---|
| S01 | 12邻域精确两hub模型；局部三/四色判别 | 证明 | [邻域](../research/factor_girth_six_neighbourhood.md) |
| S02 | 单点失败唯一高团O9；每C奇圈有单点可插代表 | 证明；多圈不自动同步 | [因子单圈](../research/factor_girth_six_ten.md)、[双高分类](../research/five_critical_high_clique_two.md)、[四高分类](../research/five_critical_high_clique_four.md) |
| S03 | 私有B8是完整组件，每组件至多阻一个坏圈点 | 证明 | [八点组件](../research/blocked_eight_component.md) |
| S04 | 私有八点旋转可任意子集同步，保持相应完整同构 | 证明；不等于同步四色 | [旋转](../research/private_eight_synchronous_rotation.md) |
| S05 | 第三势排双阻塞；反向阻塞点不相邻 | 证明，后被full版加强 | [阻塞规范化](../research/blocking_event_normalization.md)、[反向禁邻](../research/opposite_blocked_adjacency.md) |
| S06 | bowtie iff满端；第四势排双满端；相反full不邻；三连中spoke三度 | 证明，三方内部读审 | [满端规范化](../research/full_end_normalization.md) |
| S07 | 整full圈与七full连续段任意多圈同步四色 | 证明；六点弱化有列表反例 | [整圈列表](../research/all_blocked_circles_list_extension.md)、[连续段](../research/blocked_run_list_extension.md) |
| S08 | 单独可插代表两两H距离≥17时任意多点可同部插入 | 证明；不保证可选到 | [远距代表](../research/separated_good_representatives.md) |
| S09 | O9所有两代表轨道均可双圈修复 | 证明；结果未必仍最优，不能盲目迭代 | [全部轨道](../research/joint_o9_all_pairs.md) |
| S10 | 共同P3且完整邻域最大度≤2的两代表可分部修复 | 证明 | [共同路径](../research/joint_common_path_repair.md) |
| S11 | 十三点五临界核真实可实现，合格两代表均可修复 | 证明与2020原点证书；非十色反例 | [核](../research/joint_thirteen_obstruction.md)、[实现](../research/joint_thirteen_realization.md) |
| S12 | 删点C7双吹胀另一个13核，2121原点围长7实现 | 证明及端点证书；无最优分区 | [奇圈族](../research/joint_odd_cycle_blowup.md)、[实现检查](../research/joint_c7_cover_verify.py) |
| S13 | 两代表联合失败有≤44点五临界见证 | 证明及整数参数表；未全枚举 | [规模界](../research/joint_critical_size_bound.md) |
| S14 | 两O9的180个指定低点Ore合成都不满足接口 | 该有限族的纯排除及枚举 | [Ore族](../research/joint_ore_obstruction.md) |
| S15 | 指定K5/O9附件递归族至给定深度全部可修复 | 有限完整族检查；非全部临界图 | [族与两程序](../research/joint_gadget_family.md) |
| S16 | LL-O9与P3/K4十三点型搭档各为匹配 | 证明；后者不依赖第二附件完整留A | [LL匹配](../research/joint_o9_low_pair_matching.md)、[十三型匹配](../research/joint_thirteen_pair_matching.md) |
| S17 | 任意多无满端代表可一次分部，避开全部O9及指定13搭档配置 | 证明；其他核及三代表例外仍留 | [第6—7节](../research/joint_o9_low_pair_matching.md) |
| S18 | 十三点核三独立代表恰3轨道、56组三元组；剩余轨道可零势归约 | 证明；只保前两层，不保证全批次兼容 | [三代表](../research/joint_thirteen_three_representatives.md) |
| S19 | (5,4,1)每坏C边端点单独可入A五染 | 证明；平均负载不是整数选择 | [匹配路线](../research/factor_541_matching.md) |
| S20 | 两端点联合五染失败必有≤32点六临界核；含低代表时≤29 | 证明及整数表；未穷尽这些图 | [第7节](../research/factor_541_two_representatives.md)、[表核验](../research/factor_541_bound_check.py) |

## 辅助定理、方法边界和计算

| 编号 | 结论或证据 | 类型及边界 | 文件 |
|---|---|---|---|
| A01 | 私有三角条件保证最大度四K4-free图三染，高点无需独立 | 证明；额外共同邻排除不可删 | [三染](../research/private_triangle_three_colour.md)、[边界例](../research/private_triangle_repeated_centres.md) |
| A02 | k≥4私有低团条件保证k染 | 证明；去唯一high条件有25点五色例 | [私有团](../research/private_clique_colour.md) |
| A03 | K_k-free、Δ≤k+1、高点成团则k染，k≥3 | 证明 | [高团](../research/high_clique_low_clique_free.md) |
| A04 | 无K5、Δ≤5、高点成≤3团则四色 | 证明；非邻双高不能类推 | [相邻高点](../research/five_critical_two_adjacent_general.md) |
| A05 | 非邻双高九点五临界核及A五邻根降度的真实端点例 | 证明和20原点证书，可有限正规补全 | [证书程序](../research/five_critical_two_nonadjacent_endpoint.py)、[正规补全](../research/two_factor_finite_completion.md) |
| A06 | 关联权每边≥3、每点≤5的非单色超图可弱四色 | 证明 | [加权NAE](../research/weighted_nae_three.md) |
| A07 | 一些P3配对、低奇圈与K4桥树约束可统一四色 | 条件性证明及精确常数 | [混合接口](../research/mixed_path_pair_constraints.md)、[概率接口](../research/disconnected_odd_cycle_constraints.md) |
| A08 | 两个P2/P3森林的部别禁同色条件可不相容 | 五点抽象反例；未实现为目标最优分区 | [小探针](../research/two_star_forests_probe.py) |
| A09 | 普通4边染色分出的匹配冲突图有额外团和端口约束 | 证明；匹配五色未解决 | [匹配约束](../research/regular_core_matching.md)、[六色抽象障碍](../research/matching_six_obstacle.md) |
| A10 | 单次Kempe交换、单边重色、固定边界延拓可停滞 | 明确方法障碍，均非原题反例 | [三度交换](../research/degree3_continuation.md)、[正规覆盖](../research/regular_core_cover.md)、[周期列表](../research/high_girth_continuation.md) |

其余早期推导、相邻子问题、程序与中间结果全部列入 [315文件索引](FILE_INDEX.md)，没有因本表按主题合并而删除。最后尚未完成的28点加强、高团组件路线等仅在 [交接笔记](PAUSED_HANDOFF.md) 中保存，不属于本表的已证成果。
