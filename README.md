# Randić 指标与顶点温度

对每个至少有两个顶点的有限连通简单图 $G$，每个顶点 $v$ 都满足

$$R(G)\ \le\ \frac34\,\frac{2^{d(v)}}{T(v)},\qquad T(v)=\frac{d(v)}{n-d(v)}.$$

因此 Duhamel–Cazenave 语料条目 **#430943** 成立。其中对顶点取最大值的原式也可以使用系数 $3/4$，且该系数最优，三角形取等。$R(G)$ 是对无向边 $uv$ 的 $1/\sqrt{d(u)d(v)}$ 求和。

## 猜想出处与查重

Elie Duhamel 和 Tristan Cazenave 在 *Spectral Graph Theory Conjecture Generation*（2026）公开了生成语料，并在第 3 页定义了顶点温度及 Randić 指标。Tristan Cazenave 在 *Lemmas and Conjectures in Spectral Graph Theory*（2026，arXiv:2611.03879v1）第 8 节给出带状态的索引。#430943 位于该补充数据中，原始逐字陈述如下。[生成论文](https://www.lamsade.dauphine.fr/~cazenave/papers/SpectralGraphTheoryConjectureGeneration.pdf) · [后续预印本](https://arxiv.org/html/2611.03879v1#S8) · [索引压缩包](https://www.lamsade.dauphine.fr/~cazenave/papers/preuves_spectrales.zip)

> Randić ≤ max_v[((2 ^ deg(v)) / temp(v))]

2026 年 11 月 25 日检查时，该行标为 `ouverte`，已核验的公开来源中未找到对目标式的此前完整证明。近邻 #431156 的分子是 $d(v)^2$。经典的 $2R(G)\le n$ 出现在作者的证明库中。[平台、关键词、既有成果与限制](audit/search.md)

## 证明

**对边求和。** 对于任意边 $uv$，有

$$\frac{2}{\sqrt{d(u)d(v)}}\le \frac1{d(u)}+\frac1{d(v)}.$$

给每个顶点 $v$ 的每条关联边计入 $1/d(v)$，该顶点总计恰好贡献 $1$。对所有边求和得到 $2R(G)\le n$。这里 $d(v)>0$，因为图连通且 $n\ge2$。

**从图的阶数转到单个顶点。** 记 $d=d(v)$。简单图给出 $1\le d<n$，因而

$$n\le(d+1)(n-d),$$

两边之差是 $d(n-d-1)\ge0$。整数度数还满足 $2d(d+1)\le3\cdot2^d$。$d=1,2$ 可直接代入，对 $d\ge2$，从 $d$ 到 $d+1$ 时左边乘 $(d+2)/d\le2$，右边乘 $2$，归纳成立。于是

$$2nd\le2d(d+1)(n-d)\le3\cdot2^d(n-d).$$

除以 $d$ 并使用 $T(v)=d/(n-d)$，得 $2n\le3\cdot2^d/T(v)$。与边求和的估计合并，即得逐顶点界。取最大值即推出 #430943。

**最优常数。** 在 $K_3$ 中，每个顶点度为 $2$、温度为 $2$，其顶点表达式为 $2$。三条边各贡献 $1/2$，故 $R(K_3)=3/2$。任何通用上界 $R\le c\max_v 2^{d(v)}/T(v)$ 都要求 $c\ge3/4$。对于 $n=2$，两顶点度数均为 $1$，温度为 $1$，原式成为 $1\le2$。定义域上两处分母都严格为正。

## 数学陈述与 Lean 的对应

| 来源中的对象或结论 | Lean 4 表达 |
|---|---|
| 任意 $n\ge2$ 的有限连通无向简单图 | `{n : ℕ}`、`hn : 2 ≤ n`、`G : SimpleGraph (Fin n)`、`hc : G.Connected`，有限顶点上邻接可判定 |
| 度数 $d(v)$ 与温度 | `G.degree v` 与 `temperature G v`，分母为实数域上的 $n-d(v)$ |
| 无向边权 | `edgeWeight G` 用 `Sym2.lift` 实现，同一边交换端点权重不变 |
| 每条无向边恰计一次 | `randic_eq_edge_sum` 证明有向相邻对之和的一半等于原文的无向边和 |
| 最大值 | `maxScore G hn` 使用全部顶点上的 `Finset.sup'`；$n\ge2$ 给出非空证明 |
| 原始猜想 | `conjecture_430943` 及直接以无向边求和的 `conjecture_430943_edge_form` |
| 所有顶点上的锐界、三角形与最优性 | `pointwise_bound`、`triangle_values`、`optimal_constant` |

## 在本机复现

项目固定 Lean 和 Mathlib v4.36.0，Mathlib 提交为 `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`。安装 elan 后，在此目录运行下列命令。源码开启 `warningAsError`，最后的 `#print axioms` 打印关键定理的公理依赖。

```sh
lake exe cache get
lake build
lake env lean RandicTemperature.lean
lake env leanchecker RandicTemperature
python3 scripts/check_small.py
```

小图脚本在所有 2 至 6 阶连通标号图上逐顶点检验锐界，共 27,475 张。它用整数平方根构造 Randić 指标的有理上界，比较过程不依赖浮点舍入。实例中 $K_3$、$K_4$ 取等。完整结论由 Lean 证明。[Lean 源码](RandicTemperature.lean) · [构建日志](audit/build.log) · [公理输出](audit/axioms.log) · [内核重放日志](audit/kernel-replay.log) · [枚举日志](audit/small-graphs.log)
