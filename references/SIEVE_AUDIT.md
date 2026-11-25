# 上界筛与文献核对

适用对象为所有 p_i 同时为素数的一次式组。取 Q=10M_r、0≤a<Q、p=a+Qt，每个固定词产生整数式 A_i t+B_i。比值 B_i/A_i=(a+C_i/10^i)/Q 严格递增，消除比例重复。非本原式只可能等于其内容，局部不可容许组至多有 k 个参数（某式等于该处分母素数）。代码按初始末位、余因子词和唯一整性剩余类计一个分支。r=2 有 23 个可容许、3 个本原障碍、1 个非本原；r=3 分别为 49、7、8。每支的系数、公因子、行列式、E 和例外素数根数已写入 branches.json。

| 原始材料 | 本轮核验 |
|---|---|
| Ford，Sieve Methods Lecture Notes, Spring 2023，PDF 第 19 页定理 2.5 | 对非零首项、各式本原、判别乘积不为零且局部可容许的 k 个一次式给出 O_k(S x/log^k x)。固定 r 的定性结论适用于 k=2。 |
| Dubbe，arXiv:2409.04261v1，PDF 第 2–3 页定理 2 | N 为整数，筛集在 [1,N]，z=√(2N/3)，κ≥3，log N>Rκ。除有限个素数外根数恰为 κ，例外处严格较小，始终小于模数。一般式含 (1−Rκ/log N)⁻¹。 |
| Rosser–Schoenfeld，Illinois J. Math. 6 (1962)，第 71–72 页定理 15 | n≥3 的比值界；223092870 需使用 2.50637，统一上界采用该值。 |
| Bordignon–Lee，arXiv:2211.11012v1，PDF 第 14 页定理 3.4 | 需不同的不可约正首项多项式、局部可容许、(18) 的约束和小值项。作者计算脚本固定在 64d02b4008ab5a0d50423a0e2fdabbbe8900f3b9；浮点和 mpmath 输出本身不证实整个尾区间。 |

显式复核采用 N=⌊x⌋，单列 t=0，把实际正参数放大到 [1,N]。对所有 x≥exp(4R_k)，log N≥(log x)/2≥2R_k。每个 L_i(t)≥t，小素数异常只占 t≤z。E≥10^6，log E≤5k³，奇异级数≤(E/φ(E))^k≤(2 log(5k³))^k。最后一步使用定理 15 的统一界、s=log log E≥2 上的单调性和 e^γ≤exp(H16)/16<15/8。Taylor 余项检验器见 constants.py。log x≥4k² 时 x/log^k x≥√x，可吸收小参数和异常分支。所得 C(r)=40·36^r [2^(2k+1)k! (2 log(5k³))^k+3k]+4；R_k=5.961·10^14 k² log k。若 t=log x≥10^19 且 3≤k≤10^-8√(t/log t)，则 4R_k≤0.11922t。以上是对交接公式的独立推导，原第三轮报告全文仍未取得。

原文链接与逐文件 SHA-256 另见 sources.json。[Ford](https://ford126.web.illinois.edu/sieve2023.pdf) · [Dubbe](https://arxiv.org/pdf/2409.04261) · [Rosser–Schoenfeld](https://doi.org/10.1215/ijm/1255631807) · [Bordignon–Lee](https://arxiv.org/pdf/2211.11012)
