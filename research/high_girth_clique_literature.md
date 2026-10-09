# 围长至少五时强团界 7 与受限边集界 5：文献核查

核查日期：2026-10-09。本轮由用户追加授权联网，只核查这两个局部结论的先例；此前独立证明保留原有来源说明。未查阅整数 20 色命题的现有证明。

## 1. 结论分级

* **强团界 7：已有直接推论级先例。** 下面 Neethi–Saxena 的最大 neighbourly set 分类立即推出该界，虽未以“最大度 4、围长至少 5、界 7”单独列为定理。
* **受限边集界 5：此次未确认完全相同命题或可直接套用的先例。** 这只是本轮检索结果，不能据此声称新颖性。特别不能把上述最大集合替换分类直接用于指定边集 F。

这里 neighbourly set、antimatching 与本研究的强团是同一边集概念；另一些论文把“strong clique”用于顶点团与极大独立集的关系，与这里无关。

## 2. 直接推论的主要来源

Neethi K. S.、Sanjeev Saxena，*Maximum cardinality neighbourly sets in quadrilateral free graphs*，Journal of Combinatorial Optimization 33(2), 422–444 (2017)，出版社列出的在线发表日为 2015-11-03。

[出版社页面](https://link.springer.com/article/10.1007/s10878-015-9972-9)，[作者预印本](https://arxiv.org/pdf/1412.8338)，[arXiv 元数据](https://arxiv.org/abs/1412.8338)。arXiv 记录首投 2014-12-29；本次读取的 PDF 封面自动日期为 2021-06-15，因此位置以下述 PDF 的印刷页码为准。

**精确位置：§6，印刷第 13–14 页的四型总结；§7 开头在第 15 页说明替换性质。** 最大 neighbourly set 可选择为三角形三颗星的并、五圈、相邻双星，或一个中心的星加两/三条二步辐条。三条二步辐条情形会产生三角形。在无三角、无四圈且最大度 4 时，余下类型分别至多 5、7、6 条边，故最大强团至多 7。这一数值代入是本报告的推论。

原文短引（§7 开头，用于确认替换而非保持原集合）：

> another neighbourly set, of an earlier type, having at least the same cardinality.

该替换可能使用 F 外的边，也可能增加某顶点在候选边集中的度数。因此不能由此推得指定 F、最大 F 度数 2 时的界 5。论文 §7 确实讨论内部最大度 2，但其目标是替换成一般最大集合，范围不同。

## 3. 已核对的相邻结果

W. Cames van Batenburg、R. J. Kang、F. Pirot，*Strong cliques and forbidden cycles*，Indagationes Mathematicae 31(1), 64–82 (2020)。[作者 PDF](https://www.lri.fr/~fpirot/papers/strongclique.pdf)。

**Theorem 8(i)，印刷第 3 页**给 C4-free、Δ≥4 时强团数至多 3(Δ−1)。原文条件短引：“if G is C4-free, provided Δ ≥ 4.” 代入 Δ=4 是 9，属于较弱相邻结论，不能直接当作目标界 7。其 §5 分析无四圈强团，但本轮未把该证明改造成新的先例宣称。

E.-K. Cho、I. Choi、R. Kim、B. Park，*The strong clique number of graphs with forbidden cycles*。[作者预印本](https://arxiv.org/pdf/2003.10139)。

**Theorem 1.3 与 Theorem 1.4(ii)，印刷第 4 页**：取 k=2，前者对 C4-free 二部图给 2Δ−1；后者对同时无 C3、C4、C5 的图给同界。后者条件短引：“if G is also C3-free”。Δ=4 得到 7，但二者都比本研究的围长至少 5 假设更强，不能混同。

## 4. 检索范围与限制

检索使用 strong clique / neighbourly set / neighborly set / antimatching，并组合 girth、triangle-free、C4-free、maximum degree two、two-factor 等词。实际核读了上述原始文稿的相关命题与正文，也检查了 Mahdian 的多伦多大学学位论文中关于 C4-free antimatching 的结构章节及 Cames van Batenburg 的学位论文相关章节。搜索摘要、聚合站、非数学意义的 strong clique 结果未作为结论依据。

“未确认界 5 的先例”不等于已有文献中不存在。适当表述为：界 7 是此次独立重证的已知推论；界 5 目前有本研究的独立短证明，但文献地位尚未确定。
