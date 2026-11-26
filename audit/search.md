# 检索记录

2026 年 11 月 25 日核查。目标为 Duhamel–Cazenave 图论语料 #430943。为查找相同命题的其他写法，同时使用 `vertex temperature`、`Fajtlowicz temperature`、`Randić index`、`Randic`、`degree exponential` 及 $2^d(n-d)/d$。原论文固定在 arXiv:2611.03879v1。[原论文](https://arxiv.org/abs/2611.03879v1)

## 本轮选题

以下三个候选都出自 Duhamel 与 Cazenave 的 2026 年语料，并列入 Tristan Cazenave 的 arXiv:2611.03879v1 第 8 节附件。该快照中三行均为 `ouverte`。[作者状态表](https://www.lamsade.dauphine.fr/~cazenave/papers/preuves_spectrales.zip)

| 原始编号 | 形式化前的评估 |
|---|---|
| #430943，$R\le\max_v 2^{d(v)}/T(v)$ | 顶点和边两种求和都直接对应 Mathlib。可将图的全局估计降为独立的度数不等式，并用小完全图测试系数是否最优。选定。 |
| #105367，$\operatorname{rank}(L)\le\max_v(\operatorname{rank}(A)d(v))$ | 可检查邻接矩阵独立行的支撑能否覆盖顶点集；形式化需要把秩、生成空间和覆盖计数关联。 |
| #124806，$\operatorname{tr}(L)\le\operatorname{rank}(A)^{\operatorname{rank}(L)}$ | 适合矩阵大小及低阶图分情况。小阶退化与 Laplace 核维数增加了核对成本。 |

## 已选题的文献与代码核查

| 检索渠道 | 检索词和结果 |
|---|---|
| 作者生成语料 | `Conjectures.zip/open.txt` 第 24,228 行的编号和前缀表达式完全吻合。后续 `preuves_spectrales.zip/index_conjectures.csv`（位于同名顶层目录中）将本行标为 `ouverte` 和 `verifiee_lean=non`，证明和反例字段均为空。[原始数据](https://www.lamsade.dauphine.fr/~cazenave/papers/Conjectures.zip) · [状态表](https://www.lamsade.dauphine.fr/~cazenave/papers/preuves_spectrales.zip) |
| 同一语料的重复公式与证明库 | 全部 305,755 行中，有 12 条公式左侧为 Randić 指标、右侧为逐点取最大值且同时出现 `deg(v)`、`temp(v)`。唯一已证的近邻 #431156 使用 $d^2/T$，其在 $d=3$ 时比 $2^d/T$ 大。档案 3,673 个 Lean 文件中均未出现 `g430943`。档案 `RandicN.lean` 已有 $2R\le n$，本项目明确引用此经典先行界，并独立证明。[作者归档](https://www.lamsade.dauphine.fr/~cazenave/papers/preuves_spectrales.zip) |
| Google Scholar 与 arXiv | Google Scholar 浏览器检索 `"Cazenave" "430943"` 返回没有匹配的文章。arXiv 元数据 API 对相同组合返回 0 条，对原论文完整题名返回原文。[Scholar 检索](https://scholar.google.com/scholar?q=%22Cazenave%22+%22430943%22) · [arXiv 检索](https://export.arxiv.org/api/query?search_query=all:%22430943%22%20AND%20all:%22Cazenave%22) |
| 前向引用和数据出版物 | OpenAlex 记录 W7225245562 当日显示 0 条已收录引用。Semantic Scholar 有一次请求发生限流，独立先前请求返回空引用数组。DataCite 两个查询 `"430943" AND "Cazenave"` 与 `"spectral graph" AND "vertex temperature" AND "Randic"` 均无匹配。全文检索找到 Kramer 的后续论文，处理原文的 Conjecture 6(ii)，涉及两个特征值。[OpenAlex](https://api.openalex.org/works/W7225245562) · [DataCite](https://api.datacite.org/dois?query=%22430943%22%20AND%20%22Cazenave%22) · [Kramer 原文](https://hexagonmath.org/pdf/2611.00232v1) |
| 数学文献全文 | 交叉搜索温度、度数幂、Randić 指标及等价标量表达式。查到的近邻分别研究温度之和，以及基于度数的 Randić 上下界。未找到上述逐顶点不等式、最大值版本或其最优系数的直接解决。[温度指标论文](https://doi.org/10.1515/spma-2025-0045) · [Randić 上下界论文](https://doi.org/10.1155/2021/9938406) |
| GitHub | 使用认证代码搜索 `"g430943"`、`"430943" "Cazenave"` 及 `"2 ^ deg(v)" "temp(v)" "Randić"`。符号式没有命中，编号的其他命中是无关标识。以 arXiv 编号查 README 与议题后，复核 broken-conjectures、gap-is-one、diameter-radius 等相关仓库及 trureturing 对正文猜想 4、5 的解答。两个相关谱图反例仓库的本地快照中均无目标编号或温度公式。[代码查询](https://github.com/search?q=%22g430943%22&type=code) · [反例仓库](https://github.com/AmirMakir/broken-conjectures) · [谱隙仓库](https://github.com/Sulayman22S/gap-is-one) |
| MathOverflow、Lean Zulip、Mathlib | MathOverflow 搜 `g430943`、`430943 Cazenave` 及 `"Randić index" "temperature"`，各返回 0 条。Zulip 公开频道查 `g430943`、`430943`、`2611.03879`，各返回 0 条。Mathlib 固定版本的源码和参考文献中查 `g430943`、`Randić`、`randicIndex`、`randic_index`、`Fajtlowicz` 均未命中。[MathOverflow](https://api.stackexchange.com/2.3/search/advanced?site=mathoverflow&q=430943%20Cazenave) · [Lean Zulip](https://leanprover.zulipchat.com/#narrow/channels/web-public/search/g430943) · [Mathlib](https://github.com/leanprover-community/mathlib4/tree/fc4f59e577feb1a4956671bc04ac18aaaf8cd842) |

相同题名、关键词和前向引用的核查均未发现此前的完整解答。此结论限于查阅的公开来源。指标定义、AM–GM 和 $R\le n/2$ 均早已有之。首创性不由数据库零命中或 Lean 编译结果保证。

## 独立复核

2026-11-25 重新下载两份作者归档，核实原始文件第 24,228 行、公式及状态。邻近的 #431156 在后续索引中标为 `démontrée`、`verifiee_lean=non`，并列出使用的引理 `deg_range`、`randic_n`。该式的分子为 $d^2$，在 $d=3$ 时为 9，本条分子 $2^d$ 在此为 8。重新检索 3,673 份作者归档的 Lean 源文件，未找到定理名 `g430943`。[原始前缀公式](https://www.lamsade.dauphine.fr/~cazenave/papers/Conjectures.zip) · [后续状态索引](https://www.lamsade.dauphine.fr/~cazenave/papers/preuves_spectrales.zip)

Baoyindureng Wu（2014）在 Theorem 1.1 中将 $R(G)\le n/2$ 归于 Fajtlowicz，并给出等号条件为各连通分支正则且无孤点。在本文连通图域上，这等价于正则性。沿用 README 的标量估计可在纸面上刻画逐顶点界的等号。此时还须 $d=n-1$ 及 $2d(d+1)=3\cdot 2^d$。正整数解只有 $d=2,3$，所以恰为 $K_3,K_4$。源码用 $K_3$ 形式化了常数最优性。原目录式的系数为 1，由于顶点评分为正，其不等号在所有允许的图上均严格。[Wu，Theorem 1.1](https://doi.org/10.1186/1029-242X-2014-351) · [形式化](../RandicTemperature.lean)

本次从远端克隆重新执行了逐点有理上界枚举、`lake build`、源文件公理打印和 `leanchecker`。2 至 6 阶连通标号图中，存在加强式等号顶点的图数依次为 0、1、1、0、0。四个受审计声明的公理均限于 `propext`、`Classical.choice`、`Quot.sound`。[枚举程序](../scripts/check_small.py) · [公理输出](axioms.log)
