# 参考 Lean 证明研读与迁移

## 版本与核验层次

2026-11-25 直接从作者站点下载 14 个分卷，按编号拼接。其中前 13 卷各 18,000,000 字节，末卷 5,275,554 字节。总计 239,275,554 字节，逐卷及合并 SHA-256 见 original-parts.json。合并值为 9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc，与独立下载的 CocoSgt release 及 MIT 页面公布值相同。作者的四页公告已读取。[公告](https://alpo.ge/remark.pdf)

CocoSgt 镜像固定在 7cbf7a0c32fca1badf05931879a37c3f8a2b03b4，备用镜像在 ecd09ff9b4aaf6c08f2b5ef17dc49ca9648a77de。两个 src 子树的 Git tree 均为 b41b516b1f7baee4d83ced235ecc71fd43c97695。对原始压缩包中所有 175,190 个文件重算 Git blob 并逐个与第一镜像比对，比较了完整源码文件集合。另从两镜像单独下载顶层两个 Lean 文件及三个构建文件，逐一核对 SHA-256。两仓均未在仓根标注代码许可证，项目保存来源、摘要与派生索引。上游固定 Lean 4.33.1、Mathlib 0df444a360eaa60ab8c11dca51a86af692955474。独立于它的素数项目固定 Lean 4.19.0。[主镜像](https://github.com/CocoSgt/riemann-hypothesis-lean/tree/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4) · [备用镜像](https://github.com/jsmorph/rh/tree/ecd09ff9b4aaf6c08f2b5ef17dc49ca9648a77de)

原始材料的完整 import 图有 175,187 个项目模块、17,374,215 行；从 Main 递归展开可达全部项目模块。rh-imports.jsonl.gz 按模块列出其直接 import，rh-declarations.jsonl.gz 是源文本声明名索引，含 1,053,226 个行首显式声明。该计数口径不含展开后自动生成的声明、实例和别名。模块的可达性是形式化依赖的上界，某个定理的证明项有更细的依赖关系。实际细读范围列在下表，其他模块已索引。路线图固定在 e481c74135c4f0c20980f2371badbd0276ae8829，本轮对照了 Roadmap.lean、英文阅读指南第 2、4、5 步，及 outline-proofs、simplification-notes。该路线图的“由三个输入推出 RH”定理单独使用时有三个前提。[路线图](https://github.com/rh-lean-roadmap/rh-lean-roadmap/tree/e481c74135c4f0c20980f2371badbd0276ae8829)

## 五个最终命题

Main.lean 第 4、6、8、10、12 行直接给出五个证明项。Statements.lean 只 import Mathlib。前两个结论是 Mathlib 的 RH 和展开的相同命题，即 zeta 的零点除负偶数、且排除赋值约定处 1，实部为 1/2。第三个量化所有正模数、全部 Dirichlet 特征及所有 Re(s)>1/2 的 s，结论为 L 函数非零，平凡特征在 s=1 除外。第四、第五个把零点实部等于 1/2 限于 0<Re(s)<1，分别量化全部特征及本原特征。不含一般 Hecke 或自守 L 函数。四个显式谓词与 SHA 见 sources.json。[Main](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Main.lean) · [Statements](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Statements.lean)

MIT 页面标注更新至 2026-11-24 05:25 UTC。逐项对照其 SHA256SUMS 后，audit.log 所列五个顶层定理各自的传递公理都是 propext、Classical.choice、Quot.sound。环境中另有 sorryAx 等常量，五个证明的公理列表不含这些常量。报告记录了隔离重建、导出逐字节一致、nanoda、con-leche、Lean 默认及 paranoid 内核、Lean4Lean 和 4.33 比对结果；页面当时仍把 4.36 的主 Comparator 标作进行中。我们核对了源码、构建配置和上述报告所链接的审计/比较日志的哈希。上游完整导出解压后 61,570,595,788 字节，报告给出的重放规格约 70 GB 磁盘、100 GB 内存；本机整盘约 7.9 GiB，cgroup 内存 8 GiB。故本轮没有在本机重建全部 RH 源码或重放导出。这与本项目自身的本地构建分开记账。[MIT 核验](https://math.mit.edu/~drew/grh/) · [逐定理公理](https://math.mit.edu/~drew/grh/audit.log)

## 数学方法与定理卡

下列位置相对主镜像 src/。每张卡的字节哈希都在 sources.json。

| 源码与行号 | 准确命题或输入输出 | 数学机制、依赖与本题用途 |
|---|---|---|
| Supplements/Kernels/MainTheorems.lean 7–17，Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean 7–14 | everyCharacter_of_row 用强局部–整体行数据分别构造文献假设组与 VWin，再由 galoisLocalGlobalStrong_recParameter 消去该前提得到 everyCharacter。rhOfAll 由 allChi 得到。 | 追踪从条件接口到实际见证的那一行。本题的有限吸引性用具体行证书闭合；“每条坏轨道必出现足够余因子积”仍无见证。 |
| Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean 7–73 | factor_ne_zero 需要 Re(s)>0 及 p 素；prim_zero 通过升层 Euler 因子把零点传到本原特征；prim_reflect 用函数方程把 s 的零点传到逆特征的 1−s。 | 对每个被消去的因子，先用特征值模长 ≤1 和 p 的负幂严格小于 1 证明非零。对本题，在约分或取最大因子前逐一证明余因子界；将同类原理落实为 T_le_of_factorization 和上升边判别。傅里叶反射没有给 T 提供反向函数。 |
| Formalism/GammaFactorNonvanishing/CritLine.lean 11–32，ThetaPairLifts/ThirdPlaceSeries/TopPlug.lean 11–18（在 Development/AutomorphicArithmetic/ThetaCorrespondence 下） | 对本原特征，EveryCharacter 加函数方程推出临界带零点在中线上；模 1 平凡特征给 RH。TopPlug 的 zero_free_all_of_green_v_win 以 Green、VWin、Nonempty HypsAlt 为输入。 | 源码固定窗口指数 3/2，从整段窗口的界传至无零；证明需要实际供应每个特征的窗口。轨道密度界缺少从稀有轨道到整段区间的传播机制。 |
| Formalism/SharpRestriction/GrowthBounds/MultisetValuation/YEPEComm.lean 131–186 | main_ind 以分式域、p 非零、整性、交换/逐层增益条件和地点表 Nodup 为前提，对任意获准层数与整向量给出累计赋值下界。 | 归纳步把地点按谓词划开，用交换性移过已有算子，保持整性，再加上本层界。T 的时间顺序不能这样换；式 (1) 中的正实数乘积可以交换。无界轨道不重复，于是能按大小重排这些因子，推出论文定理“互异状态的乘积界”。 |
| Formalism/SharpRestriction/AdmissibleParameterJoins/SumLogPrimeFactorsLe.lean 380–389 | mu_diff 在格变更 NprimeDef、各行列式为单位、格有限生成且非零时，把斜率差精确写为有限个地点上带对数权重的赋值下取整之和。 | 先把分式理想的范数写入同一格的斜率差，再展开范数为当地因子。对本题保留每个真实余因子并使用精确恒等式 M_n p_n=10^n p+C_n，使余项的符号可追踪。没有把格斜率套用到轨道。 |
| Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean 50–65、105–160；相邻 QuotientSlopeBoundsWith.lean 34–54 | key_identity5 在正性条件下精确拆出 Main；s_lower5 与 Ga_bound5 在斜率、整除及显式预算假设下对同一量比较；ErrX5at 明列各项损失。 | 逐项计算损失后才可比较。本文在首次过界以前得到 10 C_n ≤ 9n10^n；比较 (M_n−10^n)p 与 C_n 得到可在 Lean 核验的不等式。粗略移除 C_n 在 p=17 即失败。 |
| Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChTop.lean 11–16、37–46 | 指定有限集等价和 IdentU 后，ch_top_main_eq 精确识别两边的主项；ch_top 再使用误差窗等四组输入约束点态差。 | 此方法要求被估计量完全相同。本题给定初值首次下降与连续增长段的计数是不同量，不能相互替换。 |

## 本项目固定的 Mathlib 源码

在 c44e0c8ee63ca166450922a373c7409c5d26b00b 上，Nat/Factors.lean 51–78、135–171 从分解递归证明每个成员的素性、分解乘积、成员等价于素因子及给定素分解的排列唯一性。Nat/PrimeFin.lean 30–49、65–76 以有限集合包装这些结果并判定非空。我们用其非空性取最大值，以排列唯一性把外部因子列变成内部边等式。Nat/Prime/Defs.lean 127 起把素性化为平方根内无因子，迁移为证书试除校验器。Logic/Function/Iterate.lean 60–72、163 起给出迭代方向与拼接顺序，供强归纳使用。[Factors](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/Data/Nat/Factors.lean) · [Iterate](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/Logic/Function/Iterate.lean)

## 重建索引

从作者站点合并的 lean.tar.gz 或指定镜像 release 输入 index_archive.py。传入 git -c core.quotepath=false ls-tree -r HEAD 的输出，以核对含 Unicode 的完整路径。程序先检验归档 SHA-256，再读取每个文件。可选 --declaration-index 生成完整词法声明索引。参数 --extract 指定临时目录，保存少量选读文件。闭包只统计项目内模块，外部 import 在 rh-index.json 单列。

## 首次下降窗口的再次对照

在同一固定源码上复读 ChTop.lean 第 11–68 行，ch_top_main_eq 用等价和有限求和换元识别同一个主项，ch_top 随后才把每个单位的误差估计用于该量。本轮对应的具体问题是，连续上升集合 Aᵣ 与真正的 r 步未跌破种子的集合 Sᵣ 不同。我们重新构造 Sᵣ 的余因子词和 CRT 类，得到适用于该集合的上界，再在真实轨道的分块中对同一个 Sᵣ 求和。LevelOfCongruence.lean 第 50–65、105–126 行中主项与可用误差逐项比较的做法，也用于区分短期首次下降的整数余量与 Cⱼ；这里只迁移证明结构，本项目的新不等式从 D(p) 的定义推出。[ChTop.lean](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChTop.lean)

再次从镜像的固定 Git 对象读取并逐字节对照选读件。ChTop.lean 的 SHA-256 为 9be04f7335746cae6bbdf52a813ae6713a90bf2a555eefc56f538bfd96af954f，ChainSlopeWindows/LevelOfCongruence.lean 为 b28d36820d558a77dd1b3d15fa0d8f13b130081b82f9439cc61bc676a137efd4。
