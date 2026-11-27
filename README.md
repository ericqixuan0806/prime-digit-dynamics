# prime-digit-dynamics

素数 p 的后继是 10p+(p mod 10) 的最大素因子。研究目标是证明所有素数被已知 26 周期吸引，或构造一个严格反例。当前总猜想仍待证明。

从 [阶段状态](STATUS.md)、[命题台账](THEOREMS.md)、[证明义务](OBLIGATIONS.md) 和 [研究日志](RESEARCH_LOG.md) 开始。参考 Lean 源码的版本、依赖图及数学方法见 [研读记录](references/LEAN_READING.md)。本公开仓库按所有者选择保存代码、证书与研究台账；任务书全文与论文工作稿由所有者本地保管。

## 可复现检查

在项目根目录，Python 的独立证书校验不需要第三方库。SymPy 仅用于生成因子分解、分支表及第二份短周期交叉检查。

```sh
python experiments/verify.py
python experiments/contraction.py
python experiments/reciprocal_budget.py
python experiments/survival_windows.py
python experiments/record_products.py
python experiments/orbit_constraints.py
python experiments/short_cycles.py
python experiments/constants.py
python -m pip install -r experiments/requirements.txt
python experiments/generate.py
python experiments/branches.py
python experiments/audit_cycles.py
python experiments/trial_products.py
python experiments/export_lean.py
```

Lean 使用 lean-toolchain、lakefile.toml 和 lake-manifest.json 固定版本。安装对应版本后运行以下命令。若 Mathlib 的公共缓存不可访问，Lake 可以从已固定的源码构建。

```sh
lake build
lake env lean experiments/Audit.lean
```

## 有限证书

experiments/base.tsv.gz 和 million.tsv.gz 每行依次为素数、到周期的距离、末位扩展整数的有序素因子列（含重数），三列以制表符分隔。最大因子即后继。距离零的行逐边验证完整周期，其余行严格降一。校验器还检查所有种子覆盖、全部中间节点可达、因子乘积及素性，遇到坏行即失败。million.tsv.gz 包括起点超过百万的必要中间点。

短周期证明的理论依据、余因子词的完备性和两个独立复算见 [命题台账](THEOREMS.md) 及 [审计记录](AUDIT.md)。每个数据文件的 SHA-256 见 experiments/SHA256SUMS。
