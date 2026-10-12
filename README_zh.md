# Improved Sidorenko bound 的 Lean 形式化

来源论文由 Shuyan Chen、Xinmin Hou 和 Xizhi Liu 撰写。形式化项目作者和负责维护者
为 Xizhi Liu；项目采用 Apache-2.0。论文副本位于 `paper/`。

2026-10-12，完整项目已在 macOS 和 Linux 的官方 Lean 4.35.0-rc2 工具链下
编译通过。默认沙箱 Comparator 接受了三个提交声明；Lean、NanoDa 和 con-ron
均接受证明。另行检查的 28 个声明只依赖三个标准 Lean 公理。当前证据见
`verification/RESULTS.json` 及同目录日志；`legacy-v4.19.0/` 只保留旧版本记录。

## 提交的三个结果

`Challenge.lean` 独立定义超图、全局单射嵌入、论文常数、极值数和 Turán 密度，
只导入 Mathlib。`Solution.lean` 给出同名同类型声明的证明，导入完整证明开发。
Comparator 检查以下三个结果。

1. `ImprovedSidorenko.Registry.embedding` 是正文的有限嵌入断言。对于
   `r >= 3`、至少有一条边的 F，以及 `0 < q < c_r/m^((r-1)/r)`，存在统一的 N，
   使所有 n >= N 的宿主在缺边比例满足条件时包含 F 的全局单射嵌入。
2. `ImprovedSidorenko.Registry.limit_exists` 证明通常归一化的极值数收敛。
3. `ImprovedSidorenko.Registry.main_theorem` 是关于正式定义的 Turán 密度的
   Theorem 1.1，不要求使用者提供收敛、独立性、计数或参数存在性的假设。

Challenge 中三个 `sorry` 是 Palomar 声明文件的有意占位。证明开发和 Solution
不允许占位；Challenge 不导入项目证明，Solution 也不导入 Challenge。

## 极值数与极限存在性

`Extremal.lean` 将 ex(n,F) 定义为实际 F-free 宿主的最大边数，并证明最大值可达到。
它对一个 n+1 顶点宿主逐一删去顶点，再统计剩余边数。每条 r-边被计入 n+1-r 次，
因此得到归一化极值数在 n >= r 时单调不增。该序列非负，所以收敛。

代码以 n >= r 时归一化极值数的下确界定义 Turán 密度，并证明这就是整个序列的
普通极限；没有用任意收敛序列代替经典极值对象。`TuranDensity.lean` 将既有的
统一渐近上界用于实际极值宿主，得到论文主定理。

## 正文与代码的对应

| 内容 | 文件 |
|---|---|
| 超图、合法部分映射、单射嵌入 | `Basic.lean` |
| 条件失败概率与塔式等式 | `Conditional.lean`、`KernelBridge.lean` |
| 两个势函数及更新 | `EdgePotential.lean`、`CliquePotential.lean` |
| 合法选择的比例 | `LegalChoices.lean` |
| 单步下降和有限迭代 | `Potential.lean`、`Iteration.lean`、`Embedding.lean` |
| 局部引理及实际独立性 | `LocalLemma.lean`、`Independence.lean`、`Completion.lean` |
| 全局碰撞概率 | `Collision.lean` |
| 成功有序样本的 r! 倍计数 | `Counting.lean` |
| 常数与参数选择 | `Constant.lean`、`Parameters.lean`、`Main.lean` |
| 通常二项式归一化 | `Normalization.lean` |
| 极值数与极限存在性 | `Extremal.lean` |
| 关于经典 Turán 密度的主定理 | `TuranDensity.lean` |

引言引用的外部下界、指数最优性的构造和可执行的嵌入搜索算法不在本项目范围内。

## 验证与提交

固定环境是 Lean 4.35.0-rc2 和 mathlib 的完整 commit
`065356127b1dc0016f66b7283ce0ce2c4055aa55`。先运行 `lake exe cache get`，再运行
`bash verify.sh`。Linux 环境安装 bubblewrap 后，可以运行
`bash verify.sh --comparator`；它还使用工具链附带的独立内核检查导出的证明。

`.github/workflows/ci.yml` 提供 Linux CI。生成的 `.lake/` 不应提交。
Palomar 的提交入口是 https://submit.palomar-registry.org/ ，提交时需要公开
GitHub 仓库和完整 commit SHA。本次本地整改不会自动发布仓库或注册结果。

元数据中明确区分论文作者与形式化项目作者，并披露 AI 辅助过程和实际审阅状态。
Palomar 模板验证脚本和 CI 配置的来源 commit 记录在 `formalization.yaml` 中。
