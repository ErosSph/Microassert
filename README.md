# DATEAssertion2027

An evidence-linked research framework for RTL graph matching, local contracts,
cross-region SVA composition, and formal-feedback-driven refinement.

本仓库是整理后的独立代码版本，不依赖原实验目录、个人笔记或历史输出。
它保留现有算法，不把实验编号作为公开入口/文件名。**研究原型，不声称功能验证完备。**

## 方法与目录

```text
RTL → Typed Semantic Graph → microarchitecture pattern matches → Regions
SPEC + Regions → local Contracts → deterministic SVA primitives → Local SVA
SPEC event ordering + contract interfaces → Composition IR → Composite SVA
JasperGold → proof/coverage evidence → incremental Region/Contract/composition feedback
```

| 目录 | 内容 |
|---|---|
| `dateassertion/rtl_frontend/` | pyslang 解析、类型依赖图、图模式库与匹配 |
| `dateassertion/pipeline/design_flow.py` | 初始 Local + Composite 完整流程 |
| `dateassertion/pipeline/feedback_loop.py` | 可恢复的增量反馈 |
| `dateassertion/pipeline/native_measurements.py` | Jasper 原生测量及结果收集 |
| `dateassertion/ontology/primitives.py` | 固定 SVA 原语及角色编译 |
| `dateassertion/llm/prompts/` | 语义解释、SPEC 提取、组合等提示词 |
| `dateassertion/experimental/` | Region 内绑定模板配方的独立 demo，**未替换主流程** |
| `configs/`、`examples/`、`tests/` | 可移植配置、自包含示例、离线回归 |

算法说明见 [architecture.md](docs/architecture.md)，配置见 [configuration.md](docs/configuration.md)，
验证范围见 [validation.md](docs/validation.md)。

## 1. 环境安装

推荐 Linux、Python 3.10 或更新版本。核心依赖：pyslang 11、NetworkX 3、PyYAML 6。
不需要 PyTorch、GPU、Yosys 或 LLM SDK。Z3 仅用于额外的实验前件检查。

```bash
git clone git@github.com:ErosSph/DATEAssertion2027.git
cd DATEAssertion2027
python3 -m venv .venv
source .venv/bin/activate
python -m pip install --upgrade pip
python -m pip install -e '.[dev,audit]'
python -m pytest
dateassertion --help
```

正式证明/反馈需要**自行安装并授权的 Cadence JasperGold**。本仓库不分发工具、许可证或商业手册。
测试过的工具版本为 2021.12p002，其他版本可能需要调整 Tcl 选项。

## 2. 先跑完全离线示例

```bash
dateassertion doctor --config configs/example.yaml
dateassertion analyze --config configs/example.yaml --output outputs/controller_graph
# 上一轮讨论的 Region→候选模板知识包 demo（实验功能）：
dateassertion analyze --config configs/example.yaml \
  --region-templates --output outputs/controller_templates
```

以上不调用 LLM，不需要 Jasper，也不证明 SPEC。默认 analyze 仅生成已支持的结构不变量，
不是完整的 Local/Composite 流程。`--region-templates` 才是五类 Region 知识包 demo。

输出包含 `typed_semantic_graph.json`、`regions.json`、`properties.json`、`assertions.sv`。
默认结构模式在该示例生成 1 条；实验知识包生成 36 条；没有进行断言去重。

## 3. 配置 LLM

支持 OpenAI-compatible Chat Completions JSON 接口。密钥**只从环境变量读取**，
不会读取 codex 笔记，也不要把密钥写进 YAML 或提交到 Git。

```bash
export LLM_BASE_URL='https://your-provider.example/v1'
export LLM_MODEL='your-enabled-model'
read -rs -p 'LLM API key: ' LLM_API_KEY; echo
export LLM_API_KEY
dateassertion check-llm --config configs/example.yaml
```

`check-llm` 会发送一次小型真实请求，可能计费。`.env.example` 仅为变量说明，CLI 不自动加载 `.env`。
Base URL 应包含服务商要求的前缀（如 `/v1`），**不要追加 `/chat/completions`**。

配置文件中的 `llm.provider`：

- `openai-compatible`：通用 JSON 请求，不发送服务商专用 thinking 参数。
- `qwen`：保留完整 Base URL，使用 `enable_thinking` 参数。
- `deepseek`：使用 DeepSeek thinking 参数和历史端点兼容处理。

例如使用 Qwen，复制 `configs/example.yaml` 到被 Git 忽略的 `configs/local.yaml`，设置
`llm.provider: qwen`，再设置账户实际可用的模型和 Base URL。模型名不是安装依赖，本仓库不保证账户权限。
代理默认不硬编码；可配置 `llm.proxy`，或使用系统 `HTTPS_PROXY` / `NO_PROXY`。

**数据边界：**完整流程会把选中的 SPEC 文本、RTL 片段、信号和结构证据发送到配置的 LLM 服务商。
使用私有 RTL 前请确认许可和服务商数据政策。API 调用、响应、反例等产物放在忽略目录 `outputs/`。

## 4. 配置 JasperGold

```bash
export JASPERGOLD_BIN='/path/to/jaspergold'
export CDS_LIC_FILE='/path/to/license.dat'  # 或许可证服务器配置
dateassertion formal --config configs/example.yaml \
  --properties outputs/controller_templates/properties.json \
  --output outputs/controller_formal
```

`formal` 对给定的**完整 property 列表**生成 checker 并验证，不按结果过滤。
默认 assertion proof 为 600s，proof-core 测量为 600s，整个子进程预算为 3600s。
这些参数分别配置，不能混为同一超时；见配置说明。

## 5. 完整流程与反馈

```bash
# SPEC + 图匹配 + Local + Composite + Jasper；仍会调用 LLM 和 Jasper
dateassertion run --config configs/local.yaml --output outputs/my_design --rounds 0
# 继续到 10 轮反馈，重用相同输入下已完成的 initial 和 round
dateassertion run --config configs/local.yaml --output outputs/my_design --rounds 10
```

将 `design` 的 RTL、top、clock、reset、SPEC 修改为自己的设计。
路径相对于 **YAML 文件所在目录**；RTL 列表保留顺序，宏定义文件应按正确顺序放入。
没有附带五个 CPU 的上游代码/历史断言，参见 [benchmarks.md](docs/benchmarks.md)。

主要产物：

```text
outputs/my_design/
  initial/<design_id>/    # 图、Region、SPEC、Local/Composite 候选、正式结果
  feedback/rounds/round_01/ ... round_10/
  raw_exports/round_00/ ... round_10/  # 已执行 export 的 cutoff
  input_identity.json
  resolved_config.json
  status.json
```

`raw_exports` 汇集初始及截止轮次的所有已生成 Local/Composite 记录，**不做去重，不按 Proven 筛选**。
候选选择之前的未实例化义务不属于“已生成 SVA”。反馈内部仍维护 PASS/non-vacuous 的严格组合上下文，
这与所有已生成断言的 lossless export 是两个不同集合。

```bash
# 对已有完整轮次重新汇总，不调用 LLM/Jasper
dateassertion export --config configs/local.yaml --output outputs/my_design --rounds 10
```

同一输出目录有进程锁；RTL/SPEC/配置/实现变更后应使用新目录，不能混用旧缓存。
`analyze`、`formal`、`measure` 拒绝覆盖已有实验目录。

## 6. 原生 mutation、COI、proof core、stimuli

```bash
dateassertion measure --config configs/local.yaml \
  --properties outputs/my_design/raw_exports/round_10/properties.json \
  --output outputs/my_design_metrics
# 完成后可重新解析；不启动新 Jasper 会话
dateassertion collect --config configs/local.yaml --output outputs/my_design_metrics
```

`measure` 启动三个独立 Jasper 项目，并行数受机器资源/许可证限制：

| 项目 | 当前固定预算 |
|---|---|
| assertion proof → COI → proof core | 3600s → 3600s → 不限时 |
| baseline proof → **原生 mutation** | 3600s → 28800s（8h） |
| DUT-only stimuli | 不限时 |

这是迁移保留的最终测量 profile，**不是 run/formal 的预算**。启动前评估耗时；
Tcl 和日志位于 `measurements/<项目名>/`。此命令没有源级 mutation 替代实现。
同时保留 raw 和 effective 数值，以及 checked/unchecked/undetectable/unprocessed 计数。
effective 分母不是简单固定为最大值；未处理项不能随意去掉，也不能保证 COI=100%。

## 结果解释与限制

- `PASS` 才表示工具证明；保留的历史 `TIMEOUT_ACCEPTED` 标签是未决预算状态，**不是 Proven**。
  论文应使用 `proven` 字段，不把 `accepted_correct` 当证明率。
- Proven 还要检查 vacuity、环境、SPEC 和 coverage；高证明率不等于高功能覆盖。
- 图匹配与模板库不完备；反馈不能保证发现所有未建模功能。
- 实验知识包保留已知的 HOLD 空触发和表达式位宽绑定限制，未偷偷修成高成功率版本。
- 本次整理的测试不是重新完成五个 CPU 的付费 LLM/十轮 Jasper 实验，具体测试范围见验证记录。

## 发布与许可证

本次仅整理源代码、提示词、自包含 fixture 和测试。不上传密钥、许可证、本机日志、
第三方 CPU 源码、历史实验结果、商业工具或完整 SPEC 副本。
尚未替仓库所有者选择开源许可证；公开仓库不等于已经授予任意复用许可。
如果希望以 MIT/Apache-2.0 等许可证正式开源，请由所有者确认后添加 LICENSE。
